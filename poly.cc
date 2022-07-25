/*
///////////////////////////////////////////////////////////////////////////////
(C) Copyright D 2022

COMPILE:        g++ poly.cc -o poly -std=c++11 -O3

RUN:            ./poly FILE.cnf <threads>

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
*/

#include <memory.h>
#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <signal.h>
#include <math.h>
#include <stdbool.h>
#include <locale.h>
#include "memory.h"

/* a=target variable, b=bit number to act upon 0-n */
#define BIT_SET(a,b) ((a) |= (1ULL<<(b)))
#define BIT_CLEAR(a,b) ((a) &= ~(1ULL<<(b)))
#define BIT_FLIP(a,b) ((a) ^= (1ULL<<(b)))
#define BIT_CHECK(a,b) (!!((a) & (1ULL<<(b))))        // '!!' to make sure this returns 0 or 1
#define BITMASK_SET(x, mask) ((x) |= (mask))
#define BITMASK_CLEAR(x, mask) ((x) &= (~(mask)))
#define BITMASK_FLIP(x, mask) ((x) ^= (mask))
#define BITMASK_CHECK_ALL(x, mask) (!(~(x) & (mask)))
#define BITMASK_CHECK_ANY(x, mask) ((x) & (mask))

bool            debug = false;
void            INThandler(int);       // ctrl-c handler
int             max_lits_system = 3;   //max 3-SAT
int             * cls;                 //stores the clauses (max_lits_system columns)
unsigned int    * cls_matrix;          //clause matrix, has n columns (bitwise) => which variables occure in that clause
unsigned int    * cls_bit;             //clause bit structure, has n columns    => parity of these variables
bool            * active;              //active[possibleClauseNumber]
int             n;                     //number of variables
int             m;                     //number of clauses
int             solved;                //is formula solved? UNSAT = 0; SAT = 1;

struct node {
    int id;                 //thread-id
    int *model;             //current assignment
    int *temporal;          //temp assignment for oracle (not used in production)
    int *optimal;           //best assignment and solution afterwards
};

clock_t begin;
clock_t end; 

#define TEXT_DEFAULT  "\033[0m"
#define TEXT_YELLOW   "\033[1;33m"
#define TEXT_GREEN    "\033[1;32m"
#define TEXT_RED      "\033[1;31m"
#define TEXT_BLUE     "\033[1;34m"
#define TEXT_CYAN     "\033[1;36m"
#define TEXT_WHITE    "\033[1;37m"
#define TEXT_SILVER   "\033[1;315m" 

//-------------------------------------------------------------------------------------------------------------------
// handler for CTRL-C
void  INThandler(int sig)
{
    signal(sig, SIG_IGN);
    solved=-1; //this stops all the threads
    printf("\n\n EXITTING...\n");
    signal(SIGINT, INThandler);
}
//-------------------------------------------------------------------------------------------------------------------
// print a bitstring (bitcount wide):
void printbit(unsigned int bit, int bitcount) {
    unsigned int mask = 1U << (bitcount-1); //n bits
    for (int j=0; j<bitcount; j++) {
        printf("%d",(bit & mask)?1:0);
        bit <<=1;
    }
}
//-------------------------------------------------------------------------------------------------------------------
// permutate 0111 to 1011, 1101. 1110, etc. which each is a block:
unsigned int nextblock(unsigned int v) {
    unsigned int w; // next permutation of bits
    unsigned int t = v | (v - 1); // t gets v's least significant 0 bits set to 1
    // Next set to 1 the most significant bit to change, 
    // set to 0 the least significant ones, and add the necessary 1 bits.
    w = (t + 1) | (((~t & -~t) - 1) >> (__builtin_ctz(v) + 1));
    return w;
}
//-------------------------------------------------------------------------------------------------------------------
// returns if path at block at position blockpos is in CNF:
int blockincnf(unsigned int block, int blockpos) {
    int res = -1;
    for (int i=0;i<m;i++) {
        if (block == cls_matrix[i] && blockpos == cls_bit[i]) {
            res = i;
            break;
        }
    }
    return res;
}
//-------------------------------------------------------------------------------------------------------------------
// x ^ ( x & (x-1)) : Returns the rightmost 1 in binary representation of x.

// returns if a block i at position i is in conflict with block j at position j
bool isinconflict(unsigned int block_i, int blockpos_i, unsigned int block_j, int blockpos_j) {
    bool res = false;
    // quick check - overlapping vars? if not, return no conflict
    if ( (block_i & block_j) == 0) return false;

    int cursor_i = -1;
    int cursor_j = -1;
    for (int i=0;i<=n;i++) {
        // move cursor?
        if (BIT_CHECK(block_i,i)) cursor_i++;
        if (BIT_CHECK(block_j,i)) cursor_j++;
        //both vars assigned?
        if (BIT_CHECK(block_i,i) && BIT_CHECK(block_j,i)) {
            //conflict?
            if (BIT_CHECK(blockpos_i,cursor_i) != BIT_CHECK(blockpos_j,cursor_j) ) {
                res = true;
                break;
            }
        }
    }
    //printf(" isinconflict: %d_%d/%d_%d=>%d ",block_i,blockpos_i,block_j,blockpos_j,res);
    return res;
}

//-------------------------------------------------------------------------------------------------------------------
// the main solver sequence
// polynomial runtime is maximal n^3 steps 
// returns 1 if a solution is found or -1 if no solution is found
// input: node
// output: 1 if solution is found, -1 if no solution is found
int poly(struct node *node) {
    printf("c [%d] STARTING SOLVER...\n",node->id);
    bool sat;

    /// clause path - blocks:
    unsigned int path_position = 0; 
    unsigned int path_min = 0; 
    unsigned int path_max = 0;
    //starting point is last three bits set ...000111 (=BLOCK 1)
    BIT_SET(path_min,0);   // path_min |= (1U << 0);
    BIT_SET(path_min,1);   // path_min |= (1U << 1);
    BIT_SET(path_min,2);   // path_min |= (1U << 2);
    BIT_SET(path_max,n-1); // path_max |= (1U << (n-1));
    BIT_SET(path_max,n-2); // path_max |= (1U << (n-2));
    BIT_SET(path_max,n-3); // path_max |= (1U << (n-3));
    path_position = path_min;

    printf("c [%d] FIRST BLOCK    = ",node->id); printbit(path_position,n); printf("\n");
    printf("c [%d] LAST BLOCK     = ",node->id); printbit(path_max,n); printf("\n");

    /// walk the clause path and calculate it's size (f.e. 20 vars -> 1140 blocks -> 9120 total path length ca n³=8000):
    printf("c [%d] RUN LOOP ONE TIME TO COUNT COMPLEXITY...\n",node->id);
    long long unsigned int complexity_counter = 0Ul;
    // walk each block:
    int unique_clauses_cnt = 0;
    int walking = 2;
    while (walking>0) {
        printf("\rc [%d] BLOCK: %d path_position=%u/%u",node->id, unique_clauses_cnt, path_position, path_max); //printbit(path_position,n); //printf("\n");
        // walk inside the block:
        // k-Sat variations is int 0 - 8 (000, 001, ... 111)
        for (int i=0; i<8; i++) {
            //printf(" %d: ",i); printbit(i,3); printf(": ");
            // existing in CNF?
            int existingcnfclause = blockincnf(path_position,i);
            if (existingcnfclause!=-1) {
                //printf(" <- CNF CLAUSE %d \n",existingcnfclause);    
                unique_clauses_cnt++;
            } else {
                /*unsigned int block_j = nextblock(path_position);
                for (int j=0; j<8; j++) {
                    bool conf = isinconflict(path_position,i,block_j,j);
                    if (conf) printf(" conflict with %d ",j);
                }*/
                //printf("\n");    
            }
        }
        path_position = nextblock(path_position);
        complexity_counter++;
        if (walking==1) walking = 0; //needed so we also have the last block in the loop
        if (path_position==path_max) walking = 1;
        
    }
    printf("\n");
    printf("c [%d] %llu TOTAL BLOCKS\n",node->id, complexity_counter);
    printf("c [%d] %d UNIQUE CLAUSES (OUT OF %d)\n",node->id, unique_clauses_cnt, m);

    // PREPARE SOLVER: /////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    printf("c [%d] PREPARING SOLVER...\n",node->id);

    // allocate memory for active array and set all to true:
    active = (bool *) calloc((size_t) complexity_counter*8, sizeof(bool));
    for (int i=0; i<complexity_counter*8; i++) active[i] = true;
    printf("c [%d] MEMORY ALLOCATED.\n",node->id);
    // setting active for CNF occurences:
    path_position = path_min;
    walking = 2;
    int path_loc = 0;
    while (walking>0) {
        // walk inside the block:
        for (int i=0; i<8; i++) {
            if (blockincnf(path_position,i)!=-1) {
                active[path_loc] = false;
                //printf("ACTIVE[%d] IN CNF\n",path_loc);
            }
            path_loc++;
            printf("\rc [%d] SETTTING ACTIVE FOR CNF OCCURENCES - PROGRESS %d/%lld",node->id, path_loc,complexity_counter*8);
        }
        path_position = nextblock(path_position);
        if (walking==1) walking = 0; //needed so we also have the last block in the loop
        if (path_position==path_max) walking = 1;
    }
    printf("\nc [%d] ALL ACTIVE SET FOR CNF OCCURENCES.\n",node->id);
    //printf("c ACTIVE: "); for (int i=0; i<complexity_counter*8; i++) printf("%d",active[i]); printf("\n");

    printf("c [%d] RUN SOLVING LOOP...\n",node->id);

    bool Found_j = false;
    bool Found_k = false;
    bool Found_l = false;
    bool ChangesExisting = true;

    /// SOLVING LOOP: /////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    begin = clock();
    while (ChangesExisting) {
        ChangesExisting = false;
        //i-loop:
        path_position = path_min; walking = 2; path_loc = -1;
        while (walking>0) {
            printf("c [%d] -----------------------------------------------\n",node->id);
            //printf("c [%d] BLOCK %d: ",node->id,path_loc); printbit(path_position, n); printf(" PROGRESS: %d/%lld\n",path_loc,complexity_counter*8);
            for (int i=0; i<8; i++) {
                path_loc++;
                double progress = ((path_loc/8+1)/(double)complexity_counter)*100;
                printf("c [%d] ",node->id); printf(TEXT_YELLOW); printf("BLOCK %d: ",int(path_loc/8)); printbit(path_position, n); printf("-"); printbit(i,3); printf(TEXT_DEFAULT); printf(" PROGRESS: %d/%lld (%.2f%%)\n",int(path_loc/8+1),complexity_counter,progress);
                if (debug) {printf("c ACTIVE: "); for (int i=0; i<complexity_counter*8; i++) printf("%d",active[i]); printf("\n");}
                //printf("   %d: ",i); printbit(i,3); 
                if (active[path_loc]) {
                    // j-loop: --------------------------------------------------------------------------------------------
                    Found_j = false;//bool Found_j = false;
                    int path_position_j = path_min; int walking_j = 2; int path_loc_j = -1;
                    while (walking_j>0) {
                        Found_j = false;
                        for (int j=0; j<8; j++) {
                            path_loc_j++;
                            if (debug) printf("c [%d]           i=%8d j=%8d\n",node->id, path_loc, path_loc_j);
                            //printf(" j=%d ",path_loc_j);
                            if (active[path_loc_j] && !isinconflict(path_position,i,path_position_j,j) ) {
                                // k-loop --------------------------------------------------------------------------------------------
                                Found_k = false;//bool Found_k = false;
                                int path_position_k = path_min; int walking_k = 2; int path_loc_k = -1;
                                while (walking_k>0) {
                                    Found_k = false;
                                    for (int k=0; k<8; k++) {
                                        path_loc_k++;
                                        if (debug) printf("c [%d]           i=%8d j=%8d k=%8d\n",node->id, path_loc, path_loc_j, path_loc_k);
                                        //printf(" k=%d ",path_loc_k);
                                        if (active[path_loc_k] 
                                            && !isinconflict(path_position,i,path_position_k,k) 
                                            && !isinconflict(path_position_j,j,path_position_k,k) ) {
                                            // l-loop --------------------------------------------------------------------------------------------
                                            Found_l = false;//bool Found_l = false;
                                            int path_position_l = path_min; int walking_l = 2; int path_loc_l = -1;
                                            while (walking_l>0) {
                                                Found_l = false;
                                                for (int l=0; l<8; l++) {
                                                    path_loc_l++;
                                                    end = clock();
                                                    double time_spent = (double)(end - begin) / CLOCKS_PER_SEC;
                                                    printf("\rc [%d] %8.2fs i=%8d j=%8d k=%8d l=%8d ",node->id, time_spent, path_loc, path_loc_j, path_loc_k, path_loc_l);
                                                    if (active[path_loc_l] 
                                                        && !isinconflict(path_position,i,path_position_l,l) 
                                                        && !isinconflict(path_position_j,j,path_position_l,l) 
                                                        && !isinconflict(path_position_k,k,path_position_l,l) ) {
                                                        Found_l = true;
                                                        //printf("*** DEBUG L ***");
                                                        path_loc_l = path_loc_l + (7-l);
                                                        goto next_block_l;
                                                    } else {
                                                        if (debug) printf("       l -> ACTIVE[%d] IS FALSE OR CONFLICT i,l j,l k,l\n",path_loc_l);
                                                    }
                                                }
                                                //if (!Found_l) printf("*** DEBUG NOT FOUND_L ***");
                                                if (!Found_l) goto Dont_Set_Found_k_true;
                                                next_block_l:
                                                path_position_l = nextblock(path_position_l); 
                                                if (walking_l==1) walking_l = 0; //needed so we also have the last block in the loop
                                                if (path_position_l==path_max) walking_l = 1;   
                                            }
                                            //--l --------------------------------------------------------------------------------------------
                                            Found_k = true;
                                            //printf("*** DEBUG K ***");
                                            path_loc_k = path_loc_k + (7-k);
                                            goto next_block_k;
                                        } else {
                                            if (debug) printf("       k -> ACTIVE[%d] IS FALSE OR CONFLICT i,k j,k\n",path_loc_k);
                                        }
                                    Dont_Set_Found_k_true:;    
                                    }
                                    if (!Found_k) goto Dont_Set_Found_j_true;
                                    next_block_k:
                                    path_position_k = nextblock(path_position_k); 
                                    if (walking_k==1) walking_k = 0; //needed so we also have the last block in the loop
                                    if (path_position_k==path_max) walking_k = 1;    
                                }
                                //--k --------------------------------------------------------------------------------------------
                                Found_j = true;
                                //printf("*** DEBUG J ***");
                                path_loc_j = path_loc_j + (7-j);
                                goto next_block_j;
                            } else {
                                if (debug) printf("       j -> ACTIVE[%d] IS FALSE OR CONFLICT i/j\n",path_loc_j);
                            }
                        Dont_Set_Found_j_true:;    
                        }
                        if (!Found_j) {
                            active[path_loc] = false;
                            ChangesExisting = true;
                            if (debug) printf("         -> ACTIVE[%d] SET TO FALSE\n",path_loc);
                            //printf("c ACTIVE: "); for (int i=0; i<complexity_counter*8; i++) printf("%d",active[i]); printf("\n");
                            goto Next_i;
                        } 
                        //printf("DEBUG: Found_j=%d Found_k=%d Found_l=%d\n",Found_j,Found_k,Found_l);

                        next_block_j:
                        path_position_j = nextblock(path_position_j); 
                        if (walking_j==1) walking_j = 0; //needed so we also have the last block in the loop
                        if (path_position_j==path_max) walking_j = 1;    
                    }
                    //-- j --------------------------------------------------------------------------------------------
                    
                } else {
                    if (debug) printf("       i -> ACTIVE[%d] IS FALSE\n",path_loc);
                }
                Next_i:;
            }
            path_position = nextblock(path_position); 
            if (walking==1) walking = 0; //needed so we also have the last block in the loop
            if (path_position==path_max) walking = 1;  

            //exit if all active are 0 (=unsat):
            sat = false;
            printf("c ACTIVE: "); 
            printf(TEXT_GREEN);
            for (int i=0; i<complexity_counter*8; i++) {
                if (i==(path_loc+1)) printf(TEXT_RED);
                if (i==(path_loc+9)) printf(TEXT_DEFAULT);
                printf("%d",active[i]); 
                if (active[i]) sat = true;;
            }
            printf(TEXT_DEFAULT);
            printf("\n");
            if (!sat) goto finished;

            //we can also already exit when ONE entire block is 0 (in that case all j,k,l loops will return false for that block):
            // unsat complexity should be: O = 8 * (PATHLENGTH^3)
            sat = false;
            for (int i=(path_loc-7); i<=(path_loc); i++) {
                if (active[i]) sat = true;
            }  
            if (!sat) goto finished;
        }
    }

    finished:
    end = clock();
    double time_spent = (double)(end - begin) / CLOCKS_PER_SEC;
    printf("\nc [%d] SOLVING TIME: %2fs\n",node->id, time_spent);
    
    if (sat) return 1;

    return 0;
}

//-------------------------------------------------------------------------------------------------------------------
// this functions initiates a node, runs the solving sequence and prints the result
// usually also used for multi threading
// input: thread-id
int apply(int id) {
    int i,result;
    //int id = *(int *)idT; //needed for multithreading
    printf("c [%d] Starting Thread\n",id);
    struct node node;
    //pthread_mutex_lock(&lock);
    node.id = id;
    node.temporal = (int *) calloc((size_t) n, sizeof(int));
    node.model = (int *) calloc((size_t) n, sizeof(int));
    node.optimal = (int *) calloc((size_t) n, sizeof(int));

    printf("c [%d] Memory allocated\n",id);
    
    result = poly(&node);

    // print solution:
    if (result == 1) {
        printf("\ns [%d] SATISFIABLE",id);
        for (i = 0; i < n; i++) {
            if (i % 20 == 0) {
                printf("\nv ");
            }
            printf("%i ", node.optimal[i] ? +(i + 1) : -(i + 1));
        }
        printf("0\n");
    }
    if (result == 0) {
        printf("\ns UNSATISFIABLE\n");
    }

    // free memory:
    free(node.temporal);
    free(node.model);
    free(node.optimal);

    return 1;
}

//-------------------------------------------------------------------------------------------------------------------
int main(int argc, char **argv) {
    int i, j;
    char buffer[32];

    setlocale(LC_NUMERIC, ""); //thousand point

    if (argc < 2) {
        printf("c usage: %s <instance>\n", argv[0]);
        return EXIT_FAILURE;
    }

    //signal(SIGINT, INThandler);

    printf("c --------------------------------------------\n");
    printf("c Q.POLYNOMIAL.SOLVER         \n");
    printf("c --------------------------------------------\n");
    printf("c INSTANCE  : %s\n", argv[1]);

    /// load CNF header:
    FILE *file = fopen(argv[1], "r");
    if (strcmp(buffer, "c") == 0) {
        while (strcmp(buffer, "\n") != 0) {
            fscanf(file, "%s", buffer);
        }
    }
    while (strcmp(buffer, "p") != 0) {
        fscanf(file, "%s", buffer);
    }
    fscanf(file, " cnf %i %i", &n, &m);

    printf("c VARIABLES : %'d\n", n);
    printf("c CLAUSES   : %'d\n", m);
    printf("c RATIO     : %lf\n", (double) m / n);

    /// reserve  memory - needs to be done before anything else:
    cls = (int *) calloc((size_t) m*max_lits_system, sizeof(int));
    cls_matrix = (unsigned int *) calloc((size_t) m, sizeof(unsigned int));  for (i=0;i<m;i++) cls_matrix[i] = 0;
    cls_bit = (unsigned int *) calloc((size_t) m, sizeof(unsigned int));     for (i=0;i<m;i++) cls_bit[i] = 0;
        
    /// read CNF: /////////////////////////////////////////
    int lit;
    for (i = 0; i < m; i++) {
        printf("\rc LOADING CLAUSE %d  : %3.2lf%% ",i+1, 100.0 * (i + 1) / m);
        fflush(stdout);
        j = 0; 
        do {
            fscanf(file, "%s", buffer);
            if (strcmp(buffer, "c") == 0) {
                continue;
            }
            lit = atoi(buffer);
            cls[i*max_lits_system+j] = lit;
            j++;
            printf("%d ",lit); fflush(stdout);
            
        } while (strcmp(buffer, "0") != 0);
        printf("*"); fflush(stdout);
        j--;
        if (j != max_lits_system) {
            printf("c ERROR: CLAUSE %d HAS NOT %d LITERALS.\n",i,max_lits_system);
        }
    }
    
    //fclose(file); //causes corrupted length error???
    printf("\n");

    printf("c FIRST 10 CLAUSES:\n");
    for (i = 0; i < 10; i++) {
        printf("c CLAUSE %i: ",i);
        for (j = 0; j < max_lits_system; j++) {printf(" %d",cls[i*max_lits_system+j]);}
        //printf(" CONTROL: %d %d %d",a[i],b[i],c[i]);
        printf("\n");
    }

    /// build clause matrix: /////////////////////////////////////////
    /// TODO: SORT THESE CLAUSES, WILL SPEED UP PROCESSING
    /// vars occuring in each clause are bits set to 1 (first var left to right)
    for (i=0; i<m; i++) {
        for (j=0; j<max_lits_system; j++) {
            int lit = cls[i*max_lits_system+j];
            BIT_SET(cls_matrix[i],n-(abs(lit)));  //cls_matrix[i] |= (1U << n-abs(lit));
        }
    }
    /// build clause bitset:
    /// three bits for each clause; defines the polarity of each literal in each clause
    /// example:
    /// CLAUSE: 4 -18 19 -> 101 
    /// CLAUSE: 3 18 -5  -> 110
    for (i=0; i<m; i++) {
        int litbit = 0;
        int litpos = 0;
        for (j=0; j<=n; j++) {
            // is bit set? var occurs in clause
            if (BIT_CHECK(cls_matrix[i],n-j)) {
                int var = j;
                // find polarity and set it:
                int polarity = -1;
                for (int k=0; k<max_lits_system;k++) {
                    int lit = cls[i*max_lits_system+k];
                    if (abs(lit)==var) {
                        polarity = lit > 0 ? 1:0;
                        if (polarity==1) BIT_SET(litbit,max_lits_system-1-litpos);
                        litpos++;
                    } 
                }
            }
        }
        cls_bit[i] = litbit;
    }

    /*
    printf("c FIRST 10 CLAUSE MATRIX:\n");
    for (i=0; i<10;i++) {
        printf("c CLAUSE %d: ",i);
        printbit(cls_matrix[i],n);
        printf(" -> cls_bit = ");
        printbit(cls_bit[i],3);
        printf("\n");
    }
    */

    /// start solver
    apply(0);

    /*
    mtx_init(&mutex, mtx_plain);
    
    n_threads = atoi(argv[2]);

    thrd_t *thread_id = (thrd_t *) calloc((size_t) n_threads, sizeof(thread_id));
    for (i = 0; i < n_threads; ++i) {
        if (thrd_create(thread_id + i, apply, i) != thrd_success) {
            printf("%d-th thread create error\n", i);
            return 0;
        }
    }

    for (i = 0; i < n_threads; ++i) {
        thrd_join(thread_id[i], NULL);
    }
    */
           
        //apply(5); //5 start
        /*
        pthread_mutex_init(&lock, NULL);
        pthread_t tid[n_threads];

        for (i=0; i<n_threads; i++) {
            pthread_create(&tid[i], NULL, &apply, (void*)&i);
        }
        
        for (i=0; i<n_threads; i++) {
            pthread_join(tid[i], NULL);
        }
        
        pthread_mutex_destroy(&lock);
        */
    
    // free memory:
    free(cls);
    free(cls_matrix);
    free(cls_bit);
    free(active);
    
    return EXIT_SUCCESS;
}


