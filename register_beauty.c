#include <time.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define breadth 1
#define depth 2
#define best 3
#define astar 4

#define MAX_VALUE 1000000
#define VISITED_SIZE 1000001
#define INF 1000000000
#define TIMEOUT 60

#define INCREASE 0
#define DECREASE 1
#define DOUBLE 2
#define HALF 3
#define SQUARE 4
#define ROOT 5

struct tree_node {
    int state;
    int g;
    int h;
    int f;
    struct tree_node * parent;
    int action;
};

struct solution_path {
    int action;
    int prev_state;
    int cost;
};

struct frontier_node {
    struct tree_node * n;
    struct frontier_node * previous;
    struct frontier_node * next;
};

struct frontier_node * frontier_head = NULL;
struct frontier_node * frontier_tail = NULL;
int min_g_to_state[VISITED_SIZE];
clock_t t1, t2;

int start_value;
int goal_value;
struct tree_node * solution_node = NULL;

// Reading run-time parameters.
int get_method(char * s) {
    if (strcmp(s, "breadth") == 0)
        return breadth;
    else if (strcmp(s, "depth") == 0)
        return depth;
    else if (strcmp(s, "best") == 0)
        return best;
    else if (strcmp(s, "astar") == 0)
        return astar;
    else
        return -1;
}

int is_valid_action(int action, int x) {
    if (action == INCREASE)
        return x < MAX_VALUE;
    if (action == DECREASE)
        return x > 0;
    if (action == DOUBLE)
        return (x > 0 && (long long) x * 2 <= MAX_VALUE);
    if (action == HALF)
        return x > 0;
    if (action == SQUARE)
        return (x > 1 && (long long) x * x <= MAX_VALUE);
    if (action == ROOT) {
        int r = (int) round(sqrt(x));
        return (r * r == x && x > 1);
    }
    return 0;
}

int action_cost(int action, int x) {
    if (action == INCREASE || action == DECREASE)
        return 2;
    if (action == DOUBLE)
        return (x + 1) / 2 + 1;
    if (action == HALF)
        return (x + 3) / 4 + 1;
    if (action == SQUARE)
        return (int)(((long long) x * x - x + 3) / 4) + 1;
    if (action == ROOT) {
        int r = (int) round(sqrt(x));
        return (abs(x - r) + 3) / 4 + 1;
    }
    return 1;
}

int check_with_parents(struct tree_node * new_node) {
    struct tree_node * parent = new_node -> parent;
    while (parent != NULL) {
        if (parent -> state == new_node -> state)
            return 0;
        parent = parent -> parent;
    }
    return 1;
}

int get_h(int x) {
    if (x == goal_value) return 0;
    double diff = (x > goal_value) ? (double)(x - goal_value) : (double)(goal_value - x);
    return (int) log2(diff);
}

// This function adds a pointer to a new leaf search-tree node at the front of the frontier.
// This function is called by the depth-first search algorithm.
// Inputs:
//		struct tree_node *node	: A (leaf) search-tree node.
// Output:
//		0 --> The new frontier node has been added successfully.
//		-1 --> Memory problem when inserting the new frontier node .
int add_frontier_front(struct tree_node * node) {
    // Creating the new frontier node
    struct frontier_node * new_frontier_node = (struct frontier_node * )
    malloc(sizeof(struct frontier_node));
    if (new_frontier_node == NULL)
        return -1;

    new_frontier_node -> n = node;
    new_frontier_node -> previous = NULL;
    new_frontier_node -> next = frontier_head;

    if (frontier_head == NULL) {
        frontier_head = new_frontier_node;
        frontier_tail = new_frontier_node;
    } else {
        frontier_head -> previous = new_frontier_node;
        frontier_head = new_frontier_node;
    }

    #ifdef SHOW_COMMENTS
    printf("Added to the front...\n");
    display_puzzle(node -> p);
    #endif
    return 0;
}
// This function adds a pointer to a new leaf search-tree node at the back of the frontier.
// This function is called by the breadth-first search algorithm.
// Inputs:
//		struct tree_node *node	: A (leaf) search-tree node.
// Output:
//		0 --> The new frontier node has been added successfully.
//		-1 --> Memory problem when inserting the new frontier node .
int add_frontier_back(struct tree_node * node) {
    // Creating the new frontier node
    struct frontier_node * new_frontier_node = (struct frontier_node * ) malloc(sizeof(struct frontier_node));
    if (new_frontier_node == NULL)
        return -1;

    new_frontier_node -> n = node;
    new_frontier_node -> next = NULL;
    new_frontier_node -> previous = frontier_tail;

    if (frontier_tail == NULL) {
        frontier_head = new_frontier_node;
        frontier_tail = new_frontier_node;
    } else {
        frontier_tail -> next = new_frontier_node;
        frontier_tail = new_frontier_node;
    }

    #ifdef SHOW_COMMENTS
    printf("Added to the back...\n");
    display_puzzle(node -> p);
    #endif

    return 0;
}

// This function adds a pointer to a new leaf search-tree node within the frontier.
// The frontier is always kept in increasing order wrt the f values of the corresponding
// search-tree nodes. The new frontier node is inserted in order.
// This function is called by the heuristic search algorithm.
// Inputs:
//		struct tree_node *node	: A (leaf) search-tree node.
// Output:
//		0 --> The new frontier node has been added successfully.
//		-1 --> Memory problem when inserting the new frontier node .
int add_frontier_in_order(struct tree_node * node) {
    // Creating the new frontier node
    struct frontier_node * new_frontier_node = (struct frontier_node * )
    malloc(sizeof(struct frontier_node));
    if (new_frontier_node == NULL)
        return -1;

    new_frontier_node -> n = node;
    new_frontier_node -> previous = NULL;
    new_frontier_node -> next = NULL;

    if (frontier_head == NULL) {
        frontier_head = new_frontier_node;
        frontier_tail = new_frontier_node;
    } else {
        struct frontier_node * pt;
        pt = frontier_head;

        // Search in the frontier for the first node that corresponds to either a larger f value
        // or to an equal f value but larger h value
        // Note that for the best first search algorithm, f and h values coincide.
        while (pt != NULL && (pt -> n -> f < node -> f || (pt -> n -> f == node -> f && pt -> n -> h < node -> h)))
            pt = pt -> next;

        if (pt != NULL) {
            // new_frontier_node is inserted before pt .
            if (pt -> previous != NULL) {
                pt -> previous -> next = new_frontier_node;
                new_frontier_node -> next = pt;
                new_frontier_node -> previous = pt -> previous;
                pt -> previous = new_frontier_node;
            } else {
                // In this case, new_frontier_node becomes the first node of the frontier.
                new_frontier_node -> next = pt;
                pt -> previous = new_frontier_node;
                frontier_head = new_frontier_node;
            }
        } else {
            // if pt==NULL, new_frontier_node is inserted at the back of the frontier
            frontier_tail -> next = new_frontier_node;
            new_frontier_node -> previous = frontier_tail;
            frontier_tail = new_frontier_node;
        }
    }

    #ifdef SHOW_COMMENTS
    printf("Added in order (f=%d)...\n", node -> f);
    display_puzzle(node -> p);
    #endif

    return 0;
}

// This function expands the current search-tree node by generating all valid successor
// states (children) based on the 6 available operations. It calculates the cost (g),
// heuristic (h), and priority (f) for each child according to the selected search method.
// It also applies pruning logic to discard suboptimal paths and inserts the new nodes
// into the frontier (Stack, Queue, or Priority Queue).
// This function is called by the main search loop.
// Inputs:
//		struct tree_node *current_node : The search-tree node currently being expanded.
//		int method                     : The search algorithm used (breadth, depth, best, astar).
// Output:
//		1 --> The children nodes have been generated and added successfully.
//		-1 --> Memory problem when allocating nodes or inserting into the frontier.

int find_children(struct tree_node * current_node, int method) {
    int order[] = {
        SQUARE,
        DOUBLE,
        ROOT,
        HALF,
        INCREASE,
        DECREASE
    };
    for (int i = 0; i < 6; i++) {
        int act = order[i];
        if (is_valid_action(act, current_node -> state)) {
            int next_val = (act == INCREASE) ? current_node -> state + 1 :
                (act == DECREASE) ? current_node -> state - 1 :
                (act == DOUBLE) ? current_node -> state * 2 :
                (act == HALF) ? current_node -> state / 2 :
                (act == SQUARE) ? (int)(current_node -> state * current_node -> state) :
                (int) round(sqrt(current_node -> state));

            int new_g = current_node -> g + action_cost(act, current_node -> state);

            if (method != depth && new_g >= min_g_to_state[next_val]) continue;

            struct tree_node * child = (struct tree_node * ) malloc(sizeof(struct tree_node));
            child -> state = next_val;
            child -> parent = current_node;
            child -> action = act;
            child -> g = new_g;
            child -> h = get_h(next_val);

            if (method == best) child -> f = child -> h;
            else if (method == astar) child -> f = child -> g + child -> h;
            else child -> f = child -> g;

            if (method == depth && !check_with_parents(child)) {
                free(child);
                continue;
            }

            if (method != depth) min_g_to_state[next_val] = new_g;

            int err = 0;
            if (method == depth) err = add_frontier_front(child);
            else if (method == breadth) err = add_frontier_back(child);
            else err = add_frontier_in_order(child);
            if (err < 0) return -1;
        }
    }
    return 1;
}

// This function implements at the higest level the search algorithms.
// The various search algorithms differ only in the way the insert
// new nodes into the frontier, so most of the code is commmon for all algorithms.
// Inputs:
//		Nothing, except for the global variables root, frontier_head and frontier_tail.
// Output:
//		NULL --> The problem cannot be solved
//		struct tree_node*	: A pointer to a search-tree leaf node that corresponds to a solution.
struct tree_node * search(int method) {
    while (frontier_head != NULL) {
        if (((double)(clock() - t1) / CLOCKS_PER_SEC) > TIMEOUT) {
            printf("Timeout\n");
            return NULL;
        }
        struct tree_node * current_node = frontier_head -> n;

        if (current_node -> state == goal_value)
            return current_node;

        struct frontier_node * temp = frontier_head;
        frontier_head = frontier_head -> next;
        if (frontier_head == NULL)
            frontier_tail = NULL;
        else
            frontier_head -> previous = NULL;
        free(temp);

        if (find_children(current_node, method) < 0)
            return NULL;
    }
    return NULL;
}

// This function writes the solution into a file
// Inputs:
//		char* filename	: The name of the file where the solution will be written.
// Outputs:
//		Nothing (apart from the new file)
void write_solution_to_file(char * filename, struct tree_node * node) {
    int d = 0;
    for (struct tree_node * t = node; t -> parent; t = t -> parent) d++;

    FILE * f = fopen(filename, "w");
    fprintf(f, "%d, %d\n", d, node -> g);

    struct solution_path * p = malloc(d * sizeof(struct solution_path));
    struct tree_node * curr = node;
    for (int i = d - 1; i >= 0; i--) {
        p[i].action = curr -> action;
        p[i].prev_state = curr -> parent -> state;
        p[i].cost = action_cost(curr -> action, curr -> parent -> state);
        curr = curr -> parent;
    }

    char * names[] = {
        "increase",
        "decrease",
        "double",
        "half",
        "square",
        "root"
    };
    for (int i = 0; i < d; i++)
        fprintf(f, "%s %d %d\n", names[p[i].action], p[i].prev_state, p[i].cost);

    fclose(f);
    free(p);
}

// This function initializes the search, i.e. it creates the root node of the search tree
// and the first node of the frontier.
void initialize_search(int start, int method) {
    struct tree_node * root = (struct tree_node * ) malloc(sizeof(struct tree_node));
    root -> state = start;
    root -> parent = NULL;
    root -> g = 0;
    root -> action = -1;
    root -> h = get_h(start);
    root -> f = (method == astar) ? root -> h : (method == best ? root -> h : 0);
    add_frontier_front(root);
    min_g_to_state[start] = 0;
}

int main(int argc, char ** argv) {
    if (argc != 5) return -1;
    int method = get_method(argv[1]);
    start_value = atoi(argv[2]);
    goal_value = atoi(argv[3]);

    for (int i = 0; i < VISITED_SIZE; i++) min_g_to_state[i] = INF;

    printf("Solving %s using %s...\n", argv[2], argv[1]);
    t1 = clock();
    initialize_search(start_value, method);
    solution_node = search(method);
    t2 = clock();

    if (solution_node != NULL) {
        int steps = 0;
        for (struct tree_node * v = solution_node; v -> parent; v = v -> parent) steps++;
        printf("Solution found! (%d steps)(%d cost)\n", steps, solution_node -> g);
        printf("Time spent: %f secs\n", ((float) t2 - t1) / CLOCKS_PER_SEC);
        write_solution_to_file(argv[4], solution_node);
    } else {
        printf("No solution found.\n");
    }
    return 0;
}
