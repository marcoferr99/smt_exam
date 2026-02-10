# SMT exam solution

Solution to the
[exam](https://github.com/informatica-unica/smt/blob/main/Exercises/Exam.py) of
the course: [Symbolic AI and SMT
solving](https://github.com/informatica-unica/smt).


## Building


### Requirements

- [z3](https://github.com/Z3Prover/z3)


### On Linux

An [executable](exam.out) is already present.  If it doesn't work, run `g++
-lz3 -o exam.out` to build it again.


## Description

This solution consists of three different implementations.

The first one works as described in the [exam
submission](https://github.com/informatica-unica/smt/blob/main/Exercises/Exam.py),
except that it allows repetitions in the input numbers, by using z3 arrays.

The second one works as follows.  We start with the list of numbers given as
input.  At each step, we choose two numbers in the list and replace them with
the result of one of the elementary operations applied to them, obtaining a new
list with one fewer element for the next iteration.  This way, we can obtain
combinations not possible with the first implementation, and thus we can have
better solutions in some cases.  However, z3 can be slower, as there are more
ways of combining numbers.

The third one is a variant of the first one and it is the solution of the
[optional task](https://github.com/informatica-unica/smt/blob/main/Exercises/Exam.py#L49).


## Usage

Execute `./exam.out --demo` to run specific examples that highlight the
characteristics of the three implementations.

Execute `./exam.out n1..nk g` to solve the problem with numbers n1, n2, ..., nk
and goal g, where k should be at least 2.  Add the options `-a`, `-r` to solve
with implementations 2, 3 respectively.  Implementation 1 is the default.
