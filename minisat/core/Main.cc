/*****************************************************************************************[Main.cc]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <errno.h>
#include <zlib.h>
#include <iostream>
#include <string>
#include <vector>
#include <algorithm>
#include <stdio.h>
#include <sys/stat.h>
#include <dirent.h>
#include <python3.6m/Python.h>


#include "minisat/utils/System.h"
#include "minisat/utils/ParseUtils.h"
#include "minisat/utils/Options.h"
#include "minisat/core/Dimacs.h"
#include "minisat/core/Solver.h"

#include <fstream>
#include <iostream>
//#include <minisat/tabu/solve_sat_2.h>

using namespace Minisat;

//=================================================================================================


static Solver* solver;
// Terminate by notifying the solver and back out gracefully. This is mainly to have a test-case
// for this feature of the Solver as it may take longer than an immediate call to '_exit()'.
static void SIGINT_interrupt(int) { solver->interrupt(); }

// Note that '_exit()' rather than 'exit()' has to be used. The reason is that 'exit()' calls
// destructors and may cause deadlocks if a malloc/free function happens to be running (these
// functions are guarded by locks for multithreaded use).
static void SIGINT_exit(int) {
    printf("\n"); printf("*** INTERRUPTED ***\n");
    if (solver->verbosity > 0){
        solver->printStats();
        printf("\n"); printf("*** INTERRUPTED ***\n"); }
    _exit(1); }


//=================================================================================================
// Main:
using namespace std;

int scan(Solver& S, int argc, char** argv, char* path, char* name,string data);

int64_t getSysTimeMicros2()
{
#ifdef _WIN32
    // 从1601年1月1日0:0:0:000到1970年1月1日0:0:0:000的时间(单位100ns)
#define EPOCHFILETIME   (116444736000000000UL)
    FILETIME ft;
    LARGE_INTEGER li;
    int64_t tt = 0;
    GetSystemTimeAsFileTime(&ft);
    li.LowPart = ft.dwLowDateTime;
    li.HighPart = ft.dwHighDateTime;
    // 从1970年1月1日0:0:0:000到现在的微秒数(UTC时间)
    tt = (li.QuadPart - EPOCHFILETIME) /10;
    return tt;
#else
    timeval tv;
    gettimeofday(&tv, 0);
    return (int64_t)tv.tv_sec * 1000000 + (int64_t)tv.tv_usec;
#endif // _WIN32
    return 0;
}

void printAveResToFile(char const* path,int overall_decisions ,int overall_conflict,int overall_propagations ,double overall_timecost ,
                       double overall_decision_timecost ,double overall_conflict_timecost ,double overall_propagations_timecost, double overall_delta_conflict_time ,int solved_problem_num){
    FILE *fp;
    if((fp=fopen(path,"wt+"))==NULL){
        puts("Open file failure");
        exit(0);
    }
    fprintf(fp,"Final report:\n");
    fprintf(fp,"average timecost              : %f ms\n", double(overall_timecost/solved_problem_num));
    fprintf(fp,"average conflicts             : %f / problem\n", double(overall_conflict/solved_problem_num));
    fprintf(fp,"average conflict timecost     : %f ms\n", double(overall_conflict_timecost/solved_problem_num)/1000);

    fprintf(fp,"average decisions             : %f / problem\n", double(overall_decisions/solved_problem_num));
    fprintf(fp,"average decision timecost     : %f ms\n", double(overall_decision_timecost/solved_problem_num)/1000);

    fprintf(fp,"average propagations          : %f / problem\n", double(overall_propagations/solved_problem_num));
    fprintf(fp,"average propagation timecost  : %f ms\n", double(overall_propagations_timecost/solved_problem_num)/1000);

//    printf("average scan timecost : %f ms\n", double(getSysTimeMicros2() - start_time)/1000/solved_problem_num);

    fprintf(fp,"average delta conflict time : %f ms", double(overall_delta_conflict_time)/solved_problem_num);
    fclose(fp);
}

int main(int argc, char** argv){
    printf("siwei: hi core  hello world1\n");
    cout<<(*argv)<<endl;
    setUsageHelp("USAGE: %s [options] <input-file> <result-output-file>\n\n  where input may be either in plain or gzipped DIMACS.\n");
    setX86FPUPrecision();

    DIR *dir=NULL;
    struct dirent* pDir=NULL;


//   char* dir_path = argv[1];
     char* dir_path = "/home/qc1/code/minisat_quantum/CNF/UF150-645-100/";
//            "/home/qc1/code/minisat_quantum/CNF/UUF175-753-100/"; // "/home/qc1/code/minisat_quantum/CNF/UF200-860-1000/";
//            "/Users/siwei/workspace/CNF/UF175-753-100/";
//            "../CNF/UF200-860-1000/";
    cout<<dir_path<<endl;

    dir = opendir(dir_path);

    int len = strlen(dir_path);
    string data = "";
    for(int i = len-2; i>=0; i--){
        if(dir_path[i]=='/'){
            break;
        }
        data = dir_path[i] + data;
    }

    int solved_problem_num = 0;

//    ofstream outfile("/home/qc1/minisat_quantum/log/finish_log.csv", ios::app);
//    if(!outfile.is_open())
//    {
//        cout << "open dst File  Error opening file" << endl;
//        return -1;
//    }
//    outfile << "conflict quantum learn:\t"; //tag

    int64_t start_time = getSysTimeMicros2();
//
//    int overall_decisions = 0;
//    int overall_conflict = 0;
//    int overall_propagations = 0;
//
//    double overall_timecost = 0;
//    double overall_decision_timecost = 0;
//    double overall_conflict_timecost = 0;
//    double overall_propagations_timecost = 0;
//    double overall_delta_conflict_time = 0;
//
//    int origin_overall_decisions = 0;
//    int origin_overall_conflict = 0;
//    int origin_overall_propagations = 0;
//
//    double origin_overall_timecost = 0;
//    double origin_overall_decision_timecost = 0;
//    double origin_overall_conflict_timecost = 0;
//    double origin_overall_propagations_timecost = 0;
//    double origin_overall_delta_conflict_time = 0;

//    "/home/qc1/code/minisat_quantum/CNF/UF250-1065-100/uf250-075.cnf";
    char* path = "/home/qc1/code/minisat_quantum/CNF/UF200-860-1000/uf200-023.cnf";
//
//    Solver S;
////    S.PRINT_PROCESS = true;
////    S.enableQuantum();
////    S.quantum_effect = true; //false; //
//    scan(S, argc, argv, path, pDir->d_name,data);
//    S.printResults();
//
//    Solver S1;
////    S1.PRINT_PROCESS = true;
//    S1.enableQuantum();
//    S1.quantum_effect = false; //true;
//    scan(S1, argc, argv, path, pDir->d_name, data);
//    S1.printResults();
//
//    return 0;

    int REQUIRE_PROBLEM_NUM = 100;
    if(dir == NULL)
        printf("Error! can't open this dir\n");
    else{
        while(1)
        {

            pDir = readdir(dir);

            if (pDir == NULL) break;
            if (pDir->d_type != DT_REG)  //only file are required
                continue;
//            printf("read %s\n",pDir->d_name);
//            if(solved_problem_num != 2){
//                solved_problem_num++;
//                continue;
//            }

            string dir_path_str = string(dir_path) + string(pDir->d_name);
            char* path = (char *) malloc(strlen(dir_path) + strlen(pDir->d_name) + 1);
            sprintf(path, "%s%s", dir_path, pDir->d_name);
            //dir_path_str.c_str();

            printf("++++++++++++++++++++++++++++++************************************************************************\n");
            printf("%s\n", pDir->d_name);

            int correct_result = 0;
//
//            printf("Original method:\n");
//            Solver correct_S;
//            correct_result = scan(correct_S, argc, argv, path, pDir->d_name,data);
//            vec<lbool>& correct_answer = correct_S.model;
//            correct_S.printResults();


            printf("Quantum method:\n");
            Py_Initialize();
            PyRun_SimpleString("import sys");
            PyRun_SimpleString("sys.path.append('/home/qc1/code/new/minisat_quantum/minisat/python/')");
            Solver S;
            S.enableQuantum();
            S.quantum_effect = true; //false; //
            S.fileName = pDir->d_name;
//             S.print_clause = true;
//            S.PRINT_PROCESS = true;
//            if(correct_result == 10)
//                S.correct_answer = &correct_answer;
            scan(S, argc, argv, path, pDir->d_name,data);
            S.printResults();
            Py_Finalize();
// //            assert(S.quantum_onetime_solve_number <= 1);

//             printf("\n\n\n");

//            + 0.000002 * S.quantum_count
//            double time_cost_ms = (S.my_time_cost-S.quantum_time_cost) * 1000+ 2 * S.quantum_count / 100000 - S.DLIS_timecost;
//            outfile << to_string(S.conflicts) << "|" << to_string(time_cost_ms) << "\t";
            free(path);

//            overall_conflict += S.conflicts;
//            overall_decisions += S.decisions;
//            overall_propagations += S.propagations;
//
//            overall_conflict_timecost += S.conflict_analysis_timecost;
//            overall_decision_timecost += S.decision_timecost - S.DLIS_timecost;
//            overall_propagations_timecost += S.propagations_timecost;
//            overall_timecost += time_cost_ms;
//            overall_delta_conflict_time += S.delta_conflict_time;

           /* double origin_time_cost_ms = (correct_S.my_time_cost-correct_S.quantum_time_cost) * 1000+ 2 * correct_S.quantum_count / 100000 - correct_S.DLIS_timecost;

            origin_overall_conflict += correct_S.conflicts;
            origin_overall_decisions += correct_S.decisions;
            origin_overall_propagations += correct_S.propagations;

            origin_overall_conflict_timecost += correct_S.conflict_analysis_timecost;
            origin_overall_decision_timecost += correct_S.decision_timecost - correct_S.DLIS_timecost;
            origin_overall_propagations_timecost += correct_S.propagations_timecost;
            origin_overall_timecost += origin_time_cost_ms;
            origin_overall_delta_conflict_time += correct_S.delta_conflict_time;*/

            solved_problem_num++;
            if (solved_problem_num >= REQUIRE_PROBLEM_NUM){
                break;
            }
            printf("%d has been solved\n", solved_problem_num);

        }
    }
  /*  printf("Final report:\n");
    printf("average timecost              : %f ms\n", double(overall_timecost/solved_problem_num));
    printf("average conflicts             : %f / problem\n", double(overall_conflict/solved_problem_num));
    printf("average conflict timecost     : %f ms\n", double(overall_conflict_timecost/solved_problem_num)/1000);

    printf("average decisions             : %f / problem\n", double(overall_decisions/solved_problem_num));
    printf("average decision timecost     : %f ms\n", double(overall_decision_timecost/solved_problem_num)/1000);

    printf("average propagations          : %f / problem\n", double(overall_propagations/solved_problem_num));
    printf("average propagation timecost  : %f ms\n", double(overall_propagations_timecost/solved_problem_num)/1000);

    printf("average scan timecost : %f ms\n", double(getSysTimeMicros2() - start_time)/1000/solved_problem_num);

    printf("average delta conflict time : %f ms", double(overall_delta_conflict_time)/solved_problem_num);*/


    //char const* origin_outfilepre = "/home/qc1/minisat_quantum/aveResult/sort_";
//    char const* quantum_outfilepre = "/quantum_sort_";
//    //string const&origin_cc = string(origin_outfilepre) + string(data) + string(".txt");
//    //char const* origin_resultFilePath = origin_cc.c_str();
//    string const&quantum_cc = string(quantum_outfilepre) + string(data) + string(".txt");
//    char const* quantum_resultFilePath = quantum_cc.c_str();
//    printAveResToFile(quantum_resultFilePath,overall_decisions ,overall_conflict,overall_propagations ,overall_timecost ,
//                      overall_decision_timecost ,overall_conflict_timecost ,overall_propagations_timecost, overall_delta_conflict_time ,solved_problem_num);
//    //printAveResToFile(origin_resultFilePath,origin_overall_decisions ,origin_overall_conflict,origin_overall_propagations ,origin_overall_timecost ,
//    //                  origin_overall_decision_timecost ,origin_overall_conflict_timecost ,origin_overall_propagations_timecost, origin_overall_delta_conflict_time ,solved_problem_num);
//    closedir(dir);
//    outfile << "\n";
//    outfile.close();
    return 0;
}



int scan(Solver& S, int argc, char** argv, char* path, char* name,const string data)
{
    try {
        argv[1] = path;
       char const* outfilepre = "/home/qtcp/minisat_result/uf/0928/";
       string newName = string(name);
       newName = newName.erase(newName.length()-4,4);
       string const&cc = S.quantum_effect== true?string(outfilepre) + data +"/quantum_"+ newName + string(".txt"):string(outfilepre) + data +"/"+ newName + string(".txt");
        char const* resultFilePath =  cc.c_str();

        cout<<"resultFilePath"<<resultFilePath<<endl;
////        Solver S2;
//        S.resultFilePath = resultFilePath;
//        double initial_time = cpuTime();

        // Extra options:
        //
        IntOption    verb   ("MAIN", "verb",   "Verbosity level (0=silent, 1=some, 2=more).", 1, IntRange(0, 2));
        IntOption    cpu_lim("MAIN", "cpu-lim","Limit on CPU time allowed in seconds.\n", 0, IntRange(0, INT32_MAX));
        IntOption    mem_lim("MAIN", "mem-lim","Limit on memory usage in megabytes.\n", 0, IntRange(0, INT32_MAX));
        BoolOption   strictp("MAIN", "strict", "Validate DIMACS header during parsing.", false);
        cout<<*argv<<endl;
        parseOptions(argc, argv, true);
        S.verbosity = verb;


        solver = &S;
        // Use signal handlers that forcibly quit until the solver will be able to respond to
        // interrupts:
        sigTerm(SIGINT_exit);

        // Try to set resource limits:
        if (cpu_lim != 0) limitTime(cpu_lim);
        if (mem_lim != 0) limitMemory(mem_lim);

        if (argc == 1)
            printf("Reading from standard input... Use '--help' for help.\n");
//        /home/bamboosfox/workspace/minisat/CNF/CBS_k3_n100_m403_b10/CBS_k3_n100_m403_b10_0.cnf -no-luby -rinc=1.5 -phase-saving=0 -rnd-freq=0.02
//        argv[1] = "/home/bamboosfox/workspace/minisat/CNF/CBS_k3_n100_m403_b10/CBS_k3_n100_m403_b10_0.cnf";
//        printf(argv[1]);
//        printf("\n");
        gzFile in = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
        if (in == NULL)
            printf("ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : argv[1]), exit(1);

//        if (S.verbosity > 0){
//            printf("============================[ Problem Statistics ]=============================\n");
//            printf("|                                                                             |\n"); }

        parse_DIMACS(in, S, (bool)strictp);
        gzclose(in);
        FILE* res = (argc >= 3) ? fopen(argv[2], "wb") : NULL;
//
//        if (S.verbosity > 0){
//            printf("|  Number of variables:  %12d                                         |\n", S.nVars());
//            printf("|  Number of clauses:    %12d                                         |\n", S.nClauses()); }
//
        double parsed_time = cpuTime();
//        if (S.verbosity > 0){
//            printf("|  Parse time:           %12.2f s                                       |\n", parsed_time - initial_time);
//            printf("|                                                                             |\n"); }

        // Change to signal-handlers that will only notify the solver and allow it to terminate
        // voluntarily:
        sigTerm(SIGINT_interrupt);  //??

        if (!S.simplify()){
            if (res != NULL) fprintf(res, "UNSAT\n"), fclose(res);
            if (S.verbosity > 0){
                printf("===============================================================================\n");
                printf("Solved by unit propagation\n");
                S.printStats();
            //    S.printStatsToFile();
//               S.printStatsToFile(resultFilePath);
                printf("\n"); }
            printf("UNSATISFIABLE\n");
//            exit(20);
        }

        vec<Lit> dummy;
//        lbool ret = S.solveLimited(dummy);  //S.solveLimited(dummy);
        lbool ret = S.solve(dummy)? l_True : l_False;
        if (S.verbosity > 0){
            S.printStats();
            // S.printStatsToFile();
//           S.printStatsToFile(resultFilePath);
            printf("\n"); }
        printf(ret == l_True ? "SATISFIABLE\n" : ret == l_False ? "UNSATISFIABLE\n" : "INDETERMINATE\n");
        if (res != NULL){
            if (ret == l_True){
                fprintf(res, "SAT\n");
                for (int i = 0; i < S.nVars(); i++)
                    if (S.model[i] != l_Undef)
                        fprintf(res, "%s%s%d", (i==0)?"":" ", (S.model[i]==l_True)?"":"-", i+1);
                fprintf(res, " 0\n");
            }else if (ret == l_False)
                fprintf(res, "UNSAT\n");
            else
                fprintf(res, "INDET\n");
            fclose(res);
        }

// #ifdef NDEBUG
//         exit(ret == l_True ? 10 : ret == l_False ? 20 : 0);     // (faster than "return", which will invoke the destructor for 'Solver')
// #else
        return (ret == l_True ? 10 : ret == l_False ? 20 : 0);
// #endif
    } catch (OutOfMemoryException&){
        printf("===============================================================================\n");
        printf("INDETERMINATE\n");
        exit(0);
    }
}

