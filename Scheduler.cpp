//
//  Scheduler.cpp
//  CloudSim
//
//  Created by ELMOOTAZBELLAH ELNOZAHY on 10/20/24.
//

/* Implements a version of the Greedy scheduling algorithm based on 
pseudocode discussed in class with additional modifications and considerations.

Based on an estimation of utilization and load factor as a task-servicing policy
and the consolidation of tasks on as few machines as possible to save energy while
still meeting SLA requirements.

The pseudocode is as follows:

Initialization and new requests:
Given m physical machines and n workloads
for each i in n
for each j in m
Let u be the current utilization of machine j
Let v be the load factor of job i
If u + v < 1
Place workload i in a VM on machine j
i = i + 1
end
If there are unallocated workloads: SLA violation
If there are machines with u = 0, turn them off

Workload Completion:
Assume workload i finishes on machine j
Sort all j in m in a set s in ascending order of u
For all j in s where u > 0
For all workloads i on j
For all k > j
Let u be the current utilization of machine j
Let v be the load factor of job i
If u + v < 1
Migrate workload i in a VM on machine k
i = i + 1
If no more VM’s are on machine j then turn it off and continue, else, exit
End
*/

//basic header import
#include "Scheduler.hpp"

//student-added imports
#include <algorithm> //for sorts
#include <unordered_map>


typedef enum {
    TASK_READY,
    NOW_IDLE
} WakeupProtocol_t;
#define WAKEUP_STATES 4

//struct to provide information to machines after a state change    
struct wakeup_information {
    TaskId_t task;
    WakeupProtocol_t instruction;   
};

//vector containing machines in a ready/running state
static vector<MachineId_t> active_machines;
//vector containing machines that are idle or offline
static vector<MachineId_t> idle_machines;
//number of machines actively servicing tasks
int machines_in_use = 0;

//mapping of machines to vectors containing vms on those machines
unordered_map<MachineId_t, vector<VMId_t>> vm_map;

//mapping of tasks to the VMs they are on 
unordered_map<TaskId_t, VMId_t> task_vm_map;

//map of machines to information for instructions upon wakeup from state change
unordered_map<MachineId_t, wakeup_information> wakeup_instructions;

//Constants used for algorithmic decisions/heuristics
//Percentage of memory the CPU will keep free to protect performance.
double CPU_MEMORY_SLACK = 0.1;
//Describes the power state considered "idle" or "inactive"
MachineState_t IDLE_STATE = S3;


//Returns how many million instructions per second the CPU on the machine is capable of issuing.
unsigned current_mips_rating(MachineId_t machine_id) {
    MachineInfo_t machine_info = Machine_GetInfo(machine_id);
    CPUPerformance_t current_p_state = machine_info.p_state;
    return machine_info.performance[current_p_state];
}  

//assign initial priority to a task based on its SLA requirements
Priority_t assign_priority(TaskId_t task) {
    SLAType_t task_SLA = GetTaskInfo(task).required_sla;
    if(task_SLA == SLA3) {
        //SLA3 can be starved as long as necessary, "best effort"
        return LOW_PRIORITY;
    }
    //effective highest, high priority will be used when SLA violations occur, etc
    //allows slight influence over scheduler
    return MID_PRIORITY;
}

/*Approximates the load factor of the given task.
 * The load factor is approximated as the proportion of machine CPU capability
 * that must be allocated to a task per ms in order for its completion to
 * comply with the Service Level Agreement.
*/
double task_load_factor(TaskId_t task, MachineId_t machine_id) {
    if(assign_priority(task) == LOW_PRIORITY) {
        return 0.0; //Task will be starved, can disregard CPU load
    }
    TaskInfo_t task_info = GetTaskInfo(task);
    double instructions_per_ms = task_info.remaining_instructions / (task_info.target_completion - Now());
    return instructions_per_ms / current_mips_rating(machine_id);
}

//Calculates load of attaching the VM to a given machine.
double vm_load_factor(VMId_t vm_id, MachineId_t machine_id) {
    double utilization_total = 0;
    vector<TaskId_t> active_tasks = VM_GetInfo(vm_id).active_tasks;
    for(auto task : active_tasks) {
        utilization_total += task_load_factor(task, machine_id);
    }
    return utilization_total;
}

//Approximate the utilization of the given VM on its machine.
//NOTE: This method does not take into account GPU performance boost.
double vm_utilization(VMId_t vm_id) {
    return vm_load_factor(vm_id, VM_GetInfo(vm_id).machine_id);
}

//Approximate the current utilization of the given machine.
double machine_utilization(MachineId_t machine_id) {
    double utilization_total = 0;
    vector<VMId_t> machine_vms = vm_map[machine_id];
    for(auto vm : machine_vms) {
        utilization_total += vm_utilization(vm);
    }
    return utilization_total;
}

//Determines whether the task is compatible with the hardware of the machine.
bool task_compatible(TaskId_t task, MachineId_t machine_id) {
   return RequiredCPUType(task) == Machine_GetCPUType(machine_id);
}

//Determines whether the machine can handle the load factor of the task.
bool can_handle_load(MachineId_t machine_id, TaskId_t task) {
    MachineInfo_t machine_info = Machine_GetInfo(machine_id);
    int total_memory = machine_info.memory_size;
    //keep a certain amount of memory free to protect performance
    double memory_buffer = total_memory * CPU_MEMORY_SLACK;

    //u + v calculation from pseudocode
    bool cpu_load = task_load_factor(task, machine_id) + machine_utilization(machine_id) < 1.0;
    bool mem_load = machine_info.memory_used + GetTaskMemory(task) + memory_buffer < total_memory;
    return cpu_load && mem_load;
}

/* Determines whether the task currently fits the machine based on hardware
*  compatibility (CPU/OS) and whether the machine can handle the additional
*  load of the task (u + v < 1).
*/
bool task_fits_machine(TaskId_t task, MachineId_t machine_id) {
    return task_compatible(task, machine_id) && can_handle_load(machine_id, task);
}

//Used to sort VMs on a machine in descending order of utilization.
bool vm_u_comparator(VMId_t i, VMId_t j) {
    return vm_utilization(i) > vm_utilization(j);
}

//Used to sort VMs on a machine in descending order of utilization.
bool machine_u_comparator(MachineId_t i, MachineId_t j) {
    return machine_utilization(i) > machine_utilization(j);
}

//Prioritizes whether a machine has a GPU over utilization for cases where a task
//is GPU capable.
bool machine_gpu_comparator(MachineId_t i, MachineId_t j) {
    MachineInfo_t i_info = Machine_GetInfo(i);
    MachineInfo_t j_info = Machine_GetInfo(j);
    //if machine i is gpu capable and machine j is not, prioritize i always
    return (i_info.gpus && !j_info.gpus) || machine_u_comparator(i, j);
}



//Used to sort VMs on a machine in ascending order of utilization.
bool machine_u_comparator_ascending(MachineId_t i, MachineId_t j) {
    return machine_utilization(i) < machine_utilization(j);
}

//Checks if VM is compatible with target machine.
/*
* "The new machine should be one of the same family as the current machine
* (same CPU type). An exception is generated otherwise." (from spec)
*/
bool vm_compatible(VMId_t vm_id, MachineId_t machine_id) {
    MachineId_t current_machine = VM_GetInfo(vm_id).machine_id;
    return Machine_GetCPUType(current_machine) == Machine_GetCPUType(machine_id);
}

int vm_mem_load(VMId_t vm_id) {
    int total = 0;
    for(auto task : VM_GetInfo(vm_id).active_tasks) {
        total += GetTaskMemory(task);
    }
    return total;
}

bool migration_feasible(VMId_t vm_id, MachineId_t machine_id) {
    MachineInfo_t machine_info = Machine_GetInfo(machine_id);
    int total_memory = machine_info.memory_size;
    //keep a certain amount of memory free to protect performance
    double memory_buffer = total_memory * CPU_MEMORY_SLACK;

    //u + v calculation from pseudocode
    bool cpu_load = vm_load_factor(vm_id, machine_id) + machine_utilization(machine_id) < 1.0;
    //memory buffer should make vm overhead addition redundant
    bool mem_load = machine_info.memory_used + vm_mem_load(vm_id) + memory_buffer < total_memory;
    return vm_compatible(vm_id, machine_id) && cpu_load && mem_load;
}


//initialize data structures for machines
void Scheduler::Init() {
    SimOutput("Scheduler::Init(): Total number of machines is " + to_string(Machine_GetTotal()), 3);
    SimOutput("Scheduler::Init(): Initializing scheduler", 1);
    int num_machines = Machine_GetTotal();
    //add machines to log of machines and online machines
    for(int i = 0; i < num_machines; i++) {
        machines.push_back(MachineId_t(i));
        //machines are online by default 
        active_machines.push_back(MachineId_t(i));
    }
    SimOutput("Scheduler::Init(): VM ids are " + to_string(vms[0]) + " ahd " + to_string(vms[1]), 3);
}

void Scheduler::MigrationComplete(Time_t time, VMId_t vm_id) {
    // Update your data structure. The VM now can receive new tasks
}

//Finds machines with zero utilization (inactive) and turns them off.
void handle_inactive_machines() {
    //Search for inactive machines
    for(auto iter = active_machines.begin(); iter != active_machines.end();) {
        MachineId_t cur_machine = *iter;
        if(machine_utilization(cur_machine) == 0.0) {
            vector<VMId_t> machine_vms = vm_map[cur_machine];
            for(auto vm : machine_vms) {
                VM_Shutdown(vm);
            }
            machine_vms.clear(); //finish cleaning VMs
            //erase machine from the list
            iter = active_machines.erase(iter);
            wakeup_information task_payload;
            task_payload.instruction = NOW_IDLE;
            //machine has instructions to add itself to idle list upon wakeup
            wakeup_instructions[cur_machine] = task_payload;
            Machine_SetState(cur_machine, IDLE_STATE);
        }
        ++iter;
    }
}

void Scheduler::NewTask(Time_t now, TaskId_t task_id) {
    //Iterate over active machines, sort in descending order of utilization
    //prioritize gpu capability if the task is gpu capable
    if(IsTaskGPUCapable(task_id)) {
        sort(active_machines.begin(), active_machines.end(), machine_gpu_comparator);
    } else {
        sort(active_machines.begin(), active_machines.end(), machine_u_comparator);
    }
    for(MachineId_t cur_machine : active_machines) {
        //checks if task "fits" the machine (type, u + v load calculation)
        if(task_fits_machine(task_id, cur_machine)) {
            vector<VMId_t> machine_vms = vm_map[cur_machine];
            VMId_t selected_vm;
            //sort vms in descending order of utilization
            sort(machine_vms.begin(), machine_vms.end(), vm_u_comparator);
            //iterate and select the first VM compatible with the task
            for(VMId_t cur_vm : machine_vms) {
                if(VM_GetInfo(cur_vm).vm_type == RequiredVMType(task_id)) {
                    selected_vm = cur_vm;
                    break; //compatible vm found
                }
            }
            //if no compatible VM was found, make one and attach it
            if(selected_vm == NULL) {
                VMId_t task_vm = VM_Create(RequiredVMType(task_id), RequiredCPUType(task_id));
                VM_Attach(task_vm, cur_machine);
                machine_vms.push_back(task_vm);
                selected_vm = task_vm;
            } 
            //add the task to the selected machine
            VM_AddTask(selected_vm, task_id, assign_priority(task_id));
            task_vm_map[task_id] = selected_vm;
            handle_inactive_machines();
            return;
        }
    }

    //Machine/VM pair not found; find new machine
    //Iterate over idle machines and find match
    for(int i = 0; i < idle_machines.size(); i++) {
        MachineId_t cur_machine = idle_machines[i];
        if(task_compatible(task_id, cur_machine)) {
            //give the machine information to add task when it wakes up
            wakeup_information task_payload;
            task_payload.instruction = TASK_READY;
            task_payload.task = task_id;
            //wakeup handled in StateChangeComplete
            wakeup_instructions[cur_machine] = task_payload;
            //turn on machine to a ready state
            Machine_SetState(cur_machine, S0);
            //remove machine from idle vector, on wakeup it will add itself to active
            idle_machines.erase(idle_machines.begin() + i);
            handle_inactive_machines();
            return;
        }
    }

    //If task is still not attached, find best fit possible, and prepare for SLA violation
    //Create a new VM for it so it can be migrated more easily in the future
    //Attach it to machine with the smallest load possible
    VMId_t task_vm = VM_Create(RequiredVMType(task_id), RequiredCPUType(task_id));
    for(int i = active_machines.size() - 1; i >= 0; i--) {
        MachineId_t cur_machine = active_machines[i];
        if(task_compatible(task_id, cur_machine)) {
            VM_Attach(task_vm, cur_machine);
            VM_AddTask(task_vm, task_id, HIGH_PRIORITY);
            vm_map[cur_machine].push_back(task_vm);
            task_vm_map[task_id] = task_vm;
        }
    }

    handle_inactive_machines();

    //If we get here, something has gone terribly wrong.
    //Only should be possible if a capable machine does not exist
}

void Scheduler::TaskComplete(Time_t now, TaskId_t task_id) {
    // Do any bookkeeping necessary for the data structures
    // Decide if a machine is to be turned off, slowed down, or VMs to be migrated according to your policy
    // This is an opportunity to make any adjustments to optimize performance/energy

    /*
    VMId_t task_vm = task_vm_map[task_id];
    MachineId_t task_machine = VM_GetInfo(task_vm).machine_id;  
    //Do load management/migration for all active machines 
    //Sort all j in m in a set s in ascending order of u
    sort(active_machines.begin(), active_machines.end(), machine_u_comparator_ascending);
    bool found = false;
    //for all active machines, try to migrate from lowest to highest utilization
    for(int i = 0; i < active_machines.size(); i++) {
        MachineId_t cur_machine = active_machines[i];
        //For all j machines in s where u > 0
        if(machine_utilization(cur_machine) > 0.0) {
            //For all workloads i on j
            vector<VMId_t> machine_vms = vm_map[cur_machine];
            for(int j = 0; j < machine_vms.size(); j++) {
                VMId_t vm = machine_vms[j];
                //For all k > j)
                for(int k = active_machines.size() - 1; k > i; k--) { //iterate in reverse to select high u first
                    MachineId_t target_machine = active_machines[k];
                    //if u + v < 1 (and machine is compatible)
                    if(migration_feasible(vm, target_machine)) {
                        //migrate workload i to machine k
                        //erases happen here while future iterations are still possible
                        machine_vms.erase(machine_vms.begin() + j); //remove vm entry
                        //do not consider machine being migrated to until migration is done
                        active_machines.erase(active_machines.begin() + k); 
                        VM_Migrate(vm, target_machine);
                    }
                }
            }
        }
    }
    */


    SimOutput("Scheduler::TaskComplete(): Task " + to_string(task_id) + " is complete at " + to_string(now), 4);
}

void Scheduler::PeriodicCheck(Time_t now) {
    // This method should be called from SchedulerCheck()
    // SchedulerCheck is called periodically by the simulator to allow you to monitor, make decisions, adjustments, etc.
    // Unlike the other invocations of the scheduler, this one doesn't report any specific event
    // Recommendation: Take advantage of this function to do some monitoring and adjustments as necessary

    //Monitoring happens routinely at other event calls elsewhere
}

void Scheduler::Shutdown(Time_t time) {
    // Do your final reporting and bookkeeping here.
    // Report about the total energy consumed
    // Report about the SLA compliance
    // Shutdown everything to be tidy :-)
    for(auto & vm: vms) {
        VM_Shutdown(vm);
    }
    SimOutput("SimulationComplete(): Finished!", 4);
    SimOutput("SimulationComplete(): Time is " + to_string(time), 4);
}


// Public interface below

static Scheduler Scheduler;

void InitScheduler() {
    SimOutput("InitScheduler(): Initializing scheduler", 4);
    Scheduler.Init();
}

void HandleNewTask(Time_t time, TaskId_t task_id) {
    SimOutput("HandleNewTask(): Received new task " + to_string(task_id) + " at time " + to_string(time), 4);
    Scheduler.NewTask(time, task_id);
}

void HandleTaskCompletion(Time_t time, TaskId_t task_id) {
    SimOutput("HandleTaskCompletion(): Task " + to_string(task_id) + " completed at time " + to_string(time), 4);
    Scheduler.TaskComplete(time, task_id);
}

//ideally want to avoid this in the first place
void MemoryWarning(Time_t time, MachineId_t machine_id) {
    // The simulator is alerting you that machine identified by machine_id is overcommitted
    SimOutput("MemoryWarning(): Overflow at " + to_string(machine_id) + " was detected at time " + to_string(time), 0);
}

//use to respond or do something once the migration is finished
void MigrationDone(Time_t time, VMId_t vm_id) {
    // The function is called on to alert you that migration is complete
    SimOutput("MigrationDone(): Migration of VM " + to_string(vm_id) + " was completed at time " + to_string(time), 4);
    Scheduler.MigrationComplete(time, vm_id);
}

void SchedulerCheck(Time_t time) {
    // This function is called periodically by the simulator, no specific event
    SimOutput("SchedulerCheck(): SchedulerCheck() called at " + to_string(time), 4);
    Scheduler.PeriodicCheck(time);
}

void SimulationComplete(Time_t time) {
    // This function is called before the simulation terminates Add whatever you feel like.
    cout << "SLA violation report" << endl;
    cout << "SLA0: " << GetSLAReport(SLA0) << "%" << endl;
    cout << "SLA1: " << GetSLAReport(SLA1) << "%" << endl;
    cout << "SLA2: " << GetSLAReport(SLA2) << "%" << endl;     // SLA3 do not have SLA violation issues
    cout << "Total Energy " << Machine_GetClusterEnergy() << "KW-Hour" << endl;
    cout << "Simulation run finished in " << double(time)/1000000 << " seconds" << endl;
    SimOutput("SimulationComplete(): Simulation finished at time " + to_string(time), 4);
    
    Scheduler.Shutdown(time);
}

//something in the algorithm's estimation has gone wrong
void SLAWarning(Time_t time, TaskId_t task_id) {
    //prioritize the completion of the task with the SLA violation 
    SetTaskPriority(task_id, HIGH_PRIORITY);

    /*
    VMId_t task_vm = task_vm_map[task_id];
    MachineId_t task_machine = VM_GetInfo(task_vm).machine_id;
    //perform migration
    sort(active_machines.begin(), active_machines.end(), machine_u_comparator_ascending);
    for(auto iter = active_machines.begin(); iter != active_machines.end();) {
        MachineId_t cur_machine = *iter;
        if(cur_machine != VM_GetInfo(task_vm).machine_id) {
            if(migration_feasible(task_vm, cur_machine)) {
                //migrate workload i to machine k
                vector<VMId_t> task_machine_vmlist = vm_map[task_machine];
                //first find vm in list to remove it 
                for(int i = 0; i < task_machine_vmlist.size(); i++) {
                    if(task_machine_vmlist[i] == task_vm) {
                        task_machine_vmlist.erase(task_machine_vmlist.begin() + i);
                        //do not consider machine being migrated to until migration is done
                        acstive_machines.erase(iter); 
                        VM_Migrate(task_vm, cur_machine);
                        //migration done, now we pray!
                        return;
                    }
                }
            }
        }
        ++iter;
    }
    */
}

void StateChangeComplete(Time_t time, MachineId_t machine_id) {
    wakeup_information wakeup_info = wakeup_instructions[machine_id];
    // Called in response to an earlier request to change the state of a machine
    switch(wakeup_info.instruction) {
        case TASK_READY: //this machine was turned on in NewTask to service a task
            TaskId_t task = wakeup_info.task;
            //create new vm and attach it to machine with task
            VMId_t task_vm = VM_Create(RequiredVMType(task), RequiredCPUType(task));
            VM_Attach(task_vm, machine_id);
            VM_AddTask(task_vm, task, assign_priority(task));
            vm_map[machine_id].push_back(task_vm);
            task_vm_map[task] = task_vm;
            //machine is now ready to be discoverable by algorithm
            active_machines.push_back(machine_id);
            break;
        case NOW_IDLE:
            //state change is done, make it visible to algorithm again
            idle_machines.push_back(machine_id);
            break;
        default:
            break;
    }
}

