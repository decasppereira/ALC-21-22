from model import *
import sys
from pysat.solvers import Glucose3
from pysat.card import CardEnc, EncType


class Problem:
    def __init__(self, lines):
        parseCounter = 0
        # Line 1 - Number of Runners
        self.numRunners = int(lines[parseCounter].rstrip())
        parseCounter += 1

        # Line 2 - Number of Products
        self.numProds = int(lines[parseCounter].rstrip())
        parseCounter += 1

        # Line 3 - Runners Initial Positions
        rPos = lines[parseCounter].rstrip().split()
        self.runners = [Runner(i+1, int(rPos[i])) for i in range(self.numRunners)]
        parseCounter += 1

        # Line 4 - __ Time between Products Shelves
        self.shelvesTimes = []
        l = parseCounter
        for i in range(l, l + self.numProds):
            line = [int(j) for j in lines[i].rstrip().split()]
            self.shelvesTimes.append(line)
            parseCounter += 1
            
        # Time in Conveyer Belt for Each Product
        self.products = []
        line = lines[parseCounter].rstrip().split()
        parseCounter += 1
        for i in range(self.numProds):
            self.products.append(Product(i+1, int(line[i])))

        # Number of Orders
        self.numOrders = int(lines[parseCounter].rstrip())
        parseCounter +=1

        # Each Order in format: #NumProductsInOrder 1 .. N Products IDs
        self.orders = []
        self.productInventory = dict.fromkeys([i+1 for i in range(self.numProds)], 0)
        oid = 1
        for i in range(parseCounter, parseCounter + self.numOrders):
            line = lines[i].rstrip().split()
            nProd = int(line[0])
            prods = [int(j) for j in line[1:]]
            for p in prods:
                self.productInventory[p] += 1
            self.orders.append(Order(oid, nProd, prods))
            oid +=1

        # ------------------ #
        # Encoding Variables #
        # -------------------#
        self.X = dict()
        self.translate_X = dict()

        self.P = dict()
        self.translate_P = dict()

        self.A = dict()
        self.translate_A = dict()

        self.solver = Glucose3()
        self.topLit = 0

    def createVariables(self, maxTime):
        lit = 1
        for i in range(1, self.numRunners+1):
            self.X[i] = dict()
            for p in range(1, self.numProds+1):
                self.X[i][p] = list()
                for t in range(maxTime):
                    self.X[i][p].append(lit)
                    self.translate_X[lit] = (i, p, t)
                    lit += 1

        for p in range(1, self.numProds+1):
            self.P[p] = list()
            for t in range(maxTime):
                self.P[p].append(lit)
                self.translate_P[lit] = (p, t)
                lit +=1

        for r in range(1, self.numRunners+1):
            self.A[r] = list()
            for t in range(maxTime):
                self.A[r].append(lit)
                self.translate_A[lit] = (r, t)
                lit +=1
        self.topLit = lit

    def encodeConstraints(self, maxTime):
        #1 - A runner cannot spend less than 50% of the max timespan amongst other runners
        for r in self.runners:
            for t in range(maxTime):
                for r2 in self.runners:         #TODO this can be moved to the loop below
                    if(r2.id != r.id):
                        self.solver.add_clause([-self.A[r.id][t], self.A[r2.id][t//2]])

        #2 - Runners start at time 0 in product j and never take breaks
        for r in self.runners:
            self.solver.add_clause([self.X[r.id][r.initialPos][0]])
            lit = self.A[r.id][0]
            self.solver.add_clause([lit])
            for t in range(1, maxTime):       #TODO olhar pa isto c atencao
                self.solver.add_clause([-self.A[r.id][t], self.A[r.id][t-1]]) 
            for t in range(maxTime-1):
                self.solver.add_clause([self.A[r.id][t], -self.A[r.id][t+1]])

        #3 - All products from all orders must arrive to the packaging area
        for p in self.products:
            qty = self.productInventory[p.id]
            enc = CardEnc.equals(self.P[p.id], bound = qty, top_id=self.topLit)
            for clause in enc.clauses:
                self.solver.add_clause(clause)

        #4 - Only one product arriving to the packaging area at a time
        for k in range(0, maxTime):
            literals = [p[k] for p in self.P.values()]
            enc = CardEnc.atmost(literals, bound = 1, top_id=self.topLit, encoding=EncType.pairwise)
            for clause in enc.clauses:
                self.solver.add_clause(clause)

        #5 - A runner takes t_ij time from product i to product j.
        for r in self.runners:
            for j in self.products:
                for k in range(maxTime):
                    l1 = self.X[r.id][j.id][k]
                    for j1 in self.products:
                        time = self.shelvesTimes[j.id-1][j1.id-1]
                        if (k+time)<maxTime:
                            l2 = self.X[r.id][j1.id][k+time]
                            self.solver.add_clause([-l1, l2])

                    #8 - A runner can also stop being active
                    if (k+1) < maxTime:
                        self.solver.add_clause([-l1, -self.A[r.id][k+1]])

                    #9 - A runner can only carry a product if they're active
                    self.solver.add_clause([-l1, self.A[r.id][k-1]])
                    

        #6 - A product takes c_j time from the conveyor belt to the packaging area
        for r in self.runners:
            for j in self.products:
                for k in range(1, maxTime):
                    if (k+j.beltTime) < maxTime:
                        self.solver.add_clause([-self.X[r.id][j.id][k], self.P[j.id][k+j.beltTime]])
                    else:
                        self.solver.add_clause([-self.X[r.id][j.id][k]]) #TODO check this condition

        #7 - A runner can only carry one product at a time
        for r in self.runners:
            for k in range(maxTime):
                literals = [p[k] for p in self.X[r.id].values()]
                enc = CardEnc.atmost(literals, bound = 1, top_id=self.topLit, encoding=EncType.pairwise)
                for clause in enc.clauses:
                    self.solver.add_clause(clause)

    
    def solve(self):
        print("\nSAT?", self.solver.solve())
        model = self.solver.get_model()
        print("Model:", model)


if __name__ == '__main__':
    p = Problem(sys.stdin.readlines())
    
    timebound = 11
    p.createVariables(timebound)
    p.encodeConstraints(timebound)
    p.solve()
    