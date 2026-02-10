#include<iostream>
#include<limits>
#include<optional>
#include<sstream>
#include<stdexcept>

#include "z3++.h"


using std::cerr;
using std::cin;
using std::cout;
using std::endl;
using std::optional;
using std::string;
using std::to_string;
using std::vector;

using z3::context;
using z3::expr;
using z3::func_decl_vector;
using z3::model;
using z3::solver;
using z3::sort;


// Needed to be given as arguments in some functions
expr expr_add(const expr & e1, const expr & e2) {return e1 + e2;}
expr expr_sub(const expr & e1, const expr & e2) {return e1 - e2;}
expr expr_mul(const expr & e1, const expr & e2) {return e1 * e2;}
expr expr_div(const expr & e1, const expr & e2) {return e1 / e2;}

// z3 enum type for operations
class operation_sort {
    private:
        const char * names[4];
        func_decl_vector testers;

    public:
        func_decl_vector consts;
        const sort srt;

        explicit operation_sort(context & c) :
            names{"+", "-", "*", "/"}, testers(c), consts(c),
            srt(c.enumeration_sort("operation", 4, names, consts, testers)) {};
};

class solution {
    public:
        model m;
        unsigned size; // iteration for current solution
        int result;
        int distance; // distance from the goal

        void print() const {print_impl("Distance from goal: ");}
        void print_resilient() const {print_impl("Distance from goal after attack: ");}

    protected:
        void print_impl(const string &) const;
};

void solution::print_impl(const string & distance_text) const {
    cout << "Final number: " << result << endl;
    cout << distance_text << distance << endl;
    cout << "Numbers used: " << size + 1 << endl;
}

// base class for code used by all the implementations
class counting_solver {
    public:
        bool solve_exact();
        void solve_approx();

    protected:
        // data members
        const vector<int> & nums; // input numbers
        const int goal; // input goal
        context c;
        const operation_sort Operation; // enumeration type for operations
        const sort Z; // z3 int sort
        vector<expr> operation;
        solver s;
        unsigned step = 0; // algorithm iteration number

        counting_solver(const vector<int> & n, int g) :
            nums(n), goal(g), Operation(c), Z(c.int_sort()), s(c), nums_size(int_cast(nums.size())) {}

        virtual ~counting_solver() = default;

        expr nums_to_z3_array(const string &); // return a z3 array containing the same elements as "nums"

        // "e" is meant to be a z3 int representing an index for an array
        void in_range(const expr & e) {s.add(e >= 0 && e < nums_size);}

        expr operation_cond(unsigned op) const {return operation[step] == Operation.consts[op]();}

        unsigned max_step() const {return nums.size() - 1;}
        void add_step_constr(); // add constraints for current step

    private:
        const int nums_size;

        template<typename T> static int int_cast(T);

        virtual void add_step_constr_v() = 0; // used inside "add_step_constr"
        virtual expr res() const = 0; // final result of current iteration
        virtual void print_solution(const solution &) const = 0;
};

template<typename T> int counting_solver::int_cast(T t) {
    if(t > std::numeric_limits<int>::max() || t < 2) throw std::runtime_error("Invalid number of inputs");
    return static_cast<int>(t);
}

void counting_solver::add_step_constr() {
    operation.push_back(c.constant(("operation_" + to_string(step)).c_str(), Operation.srt));
    add_step_constr_v();
}

expr counting_solver::nums_to_z3_array(const string & name) {
    expr a = c.constant(name.c_str(), c.array_sort(Z, Z));
    for (unsigned i = 0; i < nums.size(); ++i) a = store(a, i, nums[i]);
    return a;
}

bool counting_solver::solve_exact() {
    while (step < max_step()) {
        add_step_constr();

        s.push();
        s.add(res() == goal);
        if (s.check()) {
            print_solution({s.get_model(), step+1, goal, 0});
            return true;
        }
        s.pop();

        ++step;
    }

    return false;
}

void counting_solver::solve_approx() {
    optional<solution> sol;

    while (step < max_step()) {
        add_step_constr();

        while (true) {
            s.push();
            // next distance should be lower than the previous solution distance
            if (sol) s.add(abs(goal - res()) < sol->distance);

            if (!s.check()) {
                s.pop();
                break;
            }
            model n = s.get_model();
            int n_res = n.eval(res()).get_numeral_int();
            int n_dist = abs(goal - n_res);
            if (!sol || n_dist < sol->distance) sol = {n, step+1, n_res, n_dist};
            s.pop();
        }

        ++step;
    }

    if (sol) print_solution(*sol);
    else cout << "unsat" << endl;
}

class counting_solver1 : public counting_solver {
    public:
        counting_solver1(const vector<int> &, int);

        void solve_resilient();

    private:
        const expr numbers; // z3 array containing "nums" values
        const expr initial_index; // index in "numbers" of the starting number
        vector<expr> result; // final result at each step
        vector<expr> operand_index; // index in "numbers" of the operator at each step

        void print_solution_impl(const solution &) const;
        void print_solution(const solution & sol) const override {print_solution_impl(sol); sol.print();}
        void print_solution_resilient(const solution & sol) const {print_solution_impl(sol); sol.print_resilient();}

        // add operations constraints for current step
        template<typename T> void add_operations(const expr &, const expr &, T &&);

        void add_step_constr_v() override;
        expr res() const override {return result[step+1];}
};

template<typename T> void counting_solver1::add_operations(const expr & r, const expr & a, T && b) {
    s.add(
        (operation[step] == Operation.consts[0]() && r == a + b) ||
        (operation[step] == Operation.consts[1]() && r == a - b) ||
        (operation[step] == Operation.consts[2]() && r == a * b) ||
        (b != 0 && rem(a, b) == 0 && operation[step] == Operation.consts[3]() && r == a / b)
    );
}

void counting_solver1::solve_resilient() {
    vector<expr> altered_result;
    for (unsigned i = 0; i < 11; ++i) altered_result.push_back(c.int_const(("altered_result_" + to_string(i)).c_str()));

    optional<solution> sol;

    while (step < max_step()) {
        add_step_constr();
        s.push();
        for (int i = 0; i < 11; ++i) add_operations(altered_result[i], result[step], i);
        expr max_distance = abs(goal - result[step+1]);
        for (unsigned i = 0; i < 11; ++i) max_distance = max(max_distance, abs(goal - altered_result[i]));

        while (true) {
            if (sol) s.add(max_distance < sol->distance);
            if (!s.check()) break;
            model n = s.get_model();
            int n_res = n.eval(res()).get_numeral_int();
            int n_dist = n.eval(max_distance).get_numeral_int();
            if (!sol || n_dist < sol->distance) sol = {n, step+1, n_res, n_dist};
        }
        s.pop();

        ++step;
    }

    if (sol) print_solution_resilient(*sol);
    else cout << "unsat" << endl;
}

counting_solver1::counting_solver1(const vector<int> & nums, int g) : counting_solver(nums, g), numbers(nums_to_z3_array("numbers")), initial_index(c.int_const("initial_index")) {
    in_range(initial_index);

    result.push_back(c.int_const("result_0"));
    s.add(result[0] == numbers[initial_index]);
}

void counting_solver1::print_solution_impl(const solution & sol) const {
    cout << "Initial number: " << sol.m.eval(result[0]) << endl;
    for (unsigned i = 0; i < sol.size; ++i) {
        cout << "Step " << i+1 << ": operation " << sol.m.eval(operation[i])
            << " with number " << nums[sol.m.eval(operand_index[i]).get_numeral_int()]
            << " -> result " << sol.m.eval(result[i+1]) << endl;
    }
}

void counting_solver1::add_step_constr_v() {
    result.push_back(c.int_const(("result_" + to_string(step+1)).c_str()));
    operand_index.push_back(c.int_const(("operand_index_" + to_string(step)).c_str()));

    // Check that operands indices are in range and don't repeat
    in_range(operand_index[step]);
    s.add(operand_index[step] != initial_index);
    for (unsigned j = 0; j < step; ++j) s.add(operand_index[step] != operand_index[j]);

    add_operations(result[step+1], result[step], numbers[operand_index[step]]);
}

class counting_solver2 : public counting_solver {
    public:
        counting_solver2(const vector<int> & nums, int g) : counting_solver(nums, g)
            {numbers.push_back(nums_to_z3_array("numbers_0"));}

        void solve();

    private:
        vector<expr> numbers;
        vector<expr> index1;
        vector<expr> index2;

        void print_solution(const solution &) const override;

        template<typename F> expr add_operation(unsigned op, F f) const {
            return operation_cond(op) && numbers[step+1] == store(numbers[step], index1[step], f(numbers[step][index1[step]], numbers[step][index2[step]]));
        }

        void add_step_constr_v() override;
        expr res() const override {return numbers[step+1][index1[step]];}
};

void counting_solver2::print_solution(const solution & sol) const {
    for (unsigned j = 0; j < sol.size; ++ j) {
        cout << sol.m.eval(numbers[j][index1[j]]) << " " << sol.m.eval(operation[j])
            << " " << sol.m.eval(numbers[j][index2[j]]) << " = "
            << sol.m.eval(numbers[j+1][index1[j]]).get_numeral_int() << endl;
    }
    sol.print();
}

void counting_solver2::add_step_constr_v() {
    numbers.push_back(c.constant(("numbers" + to_string(step+1)).c_str(), c.array_sort(Z, Z)));
    index1.push_back(c.int_const(("index1_" + to_string(step)).c_str()));
    index2.push_back(c.int_const(("index2_" + to_string(step)).c_str()));

    // Check that operands indices are in range and don't repeat
    in_range(index1[step]);
    in_range(index2[step]);
    s.add(index1[step] != index2[step]);
    for (unsigned j = 0; j < step; ++j) {
        s.add(index1[step] != index2[j]);
        s.add(index2[step] != index2[j]);
    }

    s.add(
        add_operation(0, expr_add) || add_operation(1, expr_sub) || add_operation(2, expr_mul) ||
        (numbers[step][index2[step]] != 0 && add_operation(3, expr_div))
    );
}

void print_problem(const vector<int> & nums, int goal) {
    cout << "Numbers: ";
    for (auto it = nums.cbegin(); it != nums.cend(); ++it) {
        if (it != nums.cbegin()) cout << ", ";
        cout << *it;
    }
    cout << endl;
    cout << "Goal: " << goal << endl;
    cout << "Solution: " << endl;
}

void counting_strategy(const vector<int> & nums, int goal, bool alg2 = false) {
    print_problem(nums, goal);
    cout << endl;
    if (alg2) {
        if (!counting_solver2(nums, goal).solve_exact()) counting_solver2(nums, goal).solve_approx();
    }
    else {
        if (!counting_solver1(nums, goal).solve_exact()) counting_solver1(nums, goal).solve_approx();
    }
    cout << endl << endl;
}

void counting_strategy_resilient(const vector<int> & nums, int goal) {
    print_problem(nums, goal);
    cout << endl;
    counting_solver1(nums, goal).solve_resilient();
    cout << endl << endl;
}

void demo() {
    string i;

    cout << "Implementation 1 example:\n" << endl;
    counting_strategy({1, 3, 5, 8, 10, 50}, 462);

    cout << "Press enter to continue..." << endl;
    getline(cin, i);

    cout << "An example with repetitions:" << endl << endl;
    counting_strategy({3, 3, 8, 8, 50}, 378);
    cout << "The number 3 is used twice." << endl << endl;

    cout << "Press enter to continue..." << endl;
    getline(cin, i);

    cout << "An example of non exact solution: " << endl << endl;
    counting_strategy({4, 6, 6, 8, 8, 4}, 517);

    cout << "Press enter to continue..." << endl;
    getline(cin, i);

    cout << "Implementation 2 example:\n" << endl;
    counting_strategy({1, 3, 5, 8, 10, 50}, 462, true);

    cout << "Press enter to continue..." << endl;
    getline(cin, i);

    cout << "Implementation 1 and 2 comparison:\n" << endl;
    counting_strategy({1, 3, 5, 8, 10, 50}, 274);
    counting_strategy({1, 3, 5, 8, 10, 50}, 274, true);

    cout << "Implementation 2 gives a better solution (fewer numbers used).\n" << endl;

    cout << "Press enter to continue..." << endl;
    getline(cin, i);

    cout << "Resilient example:\n" << endl;
    counting_strategy_resilient({1, 3, 5, 8, 10, 50}, 462);
}

int main(int argc, char *argv[]) {
    bool alt = false;
    bool res = false;
    vector<int> n;
    for (int i = 1; i < argc; ++i) {
        if (string(argv[i]) == "--demo") {
            demo();
            return 0;
        }
        else if (string(argv[i]) == "-a") alt = true;
        else if (string(argv[i]) == "-r") res = true;
        else n.push_back(std::stoi(argv[i]));
    }

    if (n.size() < 3) {
        cerr << "At least two numbers and a goal required" << endl;
        return 1;
    }
    const int goal = n.back();
    n.pop_back();
    if (res) counting_strategy_resilient(n, goal);
    else counting_strategy(n, goal, alt);

    return 0;
}
