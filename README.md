# Software Tool for solving the Warehouse Packaging problem

This project consists of a software tool for solving the Warehouse Packaging problem. In order to solve this problem, we used a solver for Satisfiability (SAT), the Glucose4.

## Running and Requirements

Our project is implemented in [Python](https://www.python.org/downloads/). To run our project, you must have the following package installed:
* [Pysat](https://pypi.org/project/pysat/)

After the setup is done, the tool is now ready to be used. In order to run it, type the following command:

```
python src/project.py < <input> > <output>
```

As an example:

```
python src/project.py < instances_p1_small/enunciado1.wps  > solution.txt
```

Afterwards, comparison between our solution and the available optimal solution can be done. For the example above, comparing the solution.txt file with instances_p1_small/enunciado1.out returns True,
so our solution is the optimal one.
