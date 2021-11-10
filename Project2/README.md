# Software Tool for solving the Warehouse Packaging problem

This project consists of a software tool for solving the Warehouse Packaging problem. In order to solve this problem, we used the z3 SMT solver, namely the Optimize solver .

## Running and Requirements

Our project is implemented in [Python](https://www.python.org/downloads/). To run our project, you must have the following package installed:
* [Z3](https://pypi.org/project/z3-solver/)

After the setup is done, the tool is now ready to be used. In order to run it, type the following command:

```
python src/project.py < <input> > <output>
```

As an example:

```
python src/project.py < instances_p1_small/enunciado1.wps  > solution.txt
```

Afterwards, comparison between our solution and the available optimal solution can be done. 
For the example above, comparing both solution.txt file and input's corresponding output (enunciado1.out, in our case) can be done. If they are both equal, then our solution is the optimal one.
