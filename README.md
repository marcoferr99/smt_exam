Solution to the exam of the course: [Symbolic AI and SMT
solving](https://github.com/informatica-unica/smt).

I implement three different algorithms.

The first one works as described in the exam submission, except that it allows
repetitions in the input numbers.

The second one allows "non-sequential" operations, giving better solutions that
are not modeled by the first algorithm in some cases.

The third one is a variant of the first one and it is the solution of the
optional task.

By running the program, it is possible to:
- choose an algorithm and run it on user inserted numbers;
- run a demo that explains the algorithms with some examples.

The repo contains an [executable](exam.out), compiled on linux with the
command:
    g++ -lz3
