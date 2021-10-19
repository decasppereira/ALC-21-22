from model import *
import sys



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
        self.runners = [Runner(i+1, rPos[i]) for i in range(self.numRunners)]
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

    def encode(self, maxTime):
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


            


if __name__ == '__main__':
    p = Problem(sys.stdin.readlines())
    p.encode(3)