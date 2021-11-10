import sys
import math
import z3


class Product:
    def __init__(self, id, beltTime):
        self.id = id
        self.beltTime = beltTime

class Order:
    def __init__(self, id, numProds, prods):
        self.id = id
        self.numProds = numProds
        self.prods = prods

class Runner:
    def __init__(self, id, initialPos):
        self.id = id
        self.initialPos = initialPos

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

        self.P = dict()

        self.A = dict()

        self.solver = z3.Optimize()
        self.clauses = []

    def createVariables(self, minT, maxT):
        self.X = dict()
        self.P = dict()
        self.A = dict()

        self.time = z3.Int("T")
        self.solver.add(self.time > minT)
        self.solver.add(self.time < maxT)

        for i in range(1, self.numRunners+1):
            self.X[i] = dict()
            for o in self.orders:
                self.X[i][o.id] = dict()
                for p in o.prods:
                    self.X[i][o.id][p] = z3.Int("X_%s_%s_%s" %(i, o.id, p))
                    x = self.X[i][o.id][p]
                    self.solver.add([x<self.time])
                    self.solver.add([x>=0])


        for o in self.orders:
            self.P[o.id] = dict()
            for p in o.prods:
                self.P[o.id][p] = z3.Int("P_%s_%s" %(o.id, p))
                x = self.P[o.id][p]
                self.solver.add(1 < x) #All products must arrive
                self.solver.add(x<self.time)

        for r in range(1, self.numRunners+1):
            self.A[r] = z3.Int("A_%s" %(r))
            x = self.A[r]
            self.solver.add(0 < x) #All runners start active at time 0
            self.solver.add(x<self.time)

    def runnerPercentages(self):
        #1 - A runner cannot spend less than 50% of the max timespan amongst other runners
        for r in self.runners:
            for r2 in self.runners:         
                if(r2.id != r.id):
                    self.solver.add([self.A[r.id] >= self.A[r2.id]/2])

    def runnerActiveConstraint(self):
        for r in self.runners:
            for o in self.X[r.id]:
                for j in self.X[r.id][o]:
                    x = self.X[r.id][o][j]
                    a = self.A[r.id]
                    self.solver.add([x < a])

    def runnerInitialPosition(self):
        for r in self.runners:
            j = r.initialPos
            cls = []
            for o in self.X[r.id]:
                for j1 in self.X[r.id][o]:
                    x1 = self.X[r.id][o][j1]
                    t = self.shelvesTimes[j-1][j1-1]
                    cls.append((x1 == t))
            a = self.A[r.id]
            cls.append((a == 1))
            self.solver.add(z3.AtMost(*cls, 1))
            self.solver.add(z3.AtLeast(*cls, 1))

            for o1 in self.orders:
                for j1 in o1.prods:
                    x1 = self.X[r.id][o1.id][j1]
                    t = self.shelvesTimes[j-1][j1-1]
                    for o2 in self.orders:
                        for j2 in o2.prods:
                            x2 = self.X[r.id][o2.id][j2]
                            if (o2.id != o1.id or j2 != j1):
                                self.solver.add(
                                    z3.Implies(
                                        z3.And(x1 == t),
                                        z3.Or(x2 > x1 , x2 ==0)
                                    )
                                )
                                #X2 cant be in time interval [X1,X]
        
    def packagingAreaConstraint(self):
        for o in self.P:
            for j in self.P[o]:
                for o1 in self.P:
                    for j1  in self.P[o1]:
                        if(o!=o1 or j!=j1):
                            p = self.P[o][j]
                            p1 = self.P[o1][j1]
                            self.solver.add([p != p1 ])
           
    def conveyorBeltConstraint(self):
        for r in self.runners:
            for o in self.orders:
                for j in self.products:
                    if(j.id in o.prods):
                        x = self.X[r.id][o.id][j.id]
                        p = self.P[o.id][j.id]
                        self.solver.add( 
                            z3.Implies(
                                x!=0,
                                p == x + j.beltTime))

    def runnerOneProductAtATime(self):
        for r in self.runners:
           for o in self.X[r.id]:
            for j in self.X[r.id][o]:
                for o1 in self.X[r.id]:
                    for j1  in self.X[r.id][o1]:
                        if(o!=o1 or j!=j1):
                            p = self.X[r.id][o][j]
                            p1 = self.X[r.id][o1][j1]
                            self.solver.add(
                                z3.Implies(
                                    z3.Or(p!=0, p1!=0),
                                    p != p1))

    def runnerIsBusyConstraint(self):
        for r in self.runners:
            for o in self.orders:
                for j in o.prods:
                    x = self.X[r.id][o.id][j]
                    for o1 in self.orders:
                        for j1 in o1.prods:
                            if (o1.id != o.id or j != j1):
                                 x1 = self.X[r.id][o1.id][j1]
                                 t = self.shelvesTimes[j-1][j1-1]
                                 for o2 in self.orders:
                                     for j2 in o2.prods:
                                         x2 = self.X[r.id][o2.id][j2]
                                         if ((o2.id != o1.id or j2 != j1) and (j2 != j or o2.id != o.id)):
                                             self.solver.add(
                                                 z3.Implies(
                                                     z3.And(x == x1 + t, x1 != 0, x != 0),
                                                     z3.Or(x2 > x , x2 < x1)
                                                 )
                                             )
                                             #X2 cant be in time interval [X1,X] 

    def productTransitionsConstraint(self):
        for r in self.runners:
            for o in self.X[r.id]:
                for j in self.X[r.id][o]:
                    x = self.X[r.id][o][j]
                    cls = []
                    for o1 in self.X[r.id]:
                        for j1 in self.X[r.id][o1]:
                            if(o!= o1  or j!=j1):
                                x1 = self.X[r.id][o1][j1]
                                t = self.shelvesTimes[j-1][j1-1]
                                cls.append((x1 == x + t))
                    #cls.append((x==0))
                    a = self.A[r.id]
                    cls.append((a == x + 1))
                    self.solver.add(z3.Implies(x!=0, 
                                        z3.AtMost(*cls, 1))) 

                    self.solver.add(z3.Implies(x!=0, 
                                    z3.AtLeast(*cls, 1)))
              
    def productDeliveredByOneRunner(self):
        for o in self.orders:
            for j in o.prods:
                cls = []
                for r in self.runners:
                    x = self.X[r.id][o.id][j]
                    cls.append(x!=0)
                self.solver.add(z3.AtMost(*cls, 1)) 
                self.solver.add(z3.AtLeast(*cls, 1))
        
    def breakProductSym(self):
        prodSequence = dict()
        for p in self.products:
            prodSequence[p.id] = []

        # prodSequence[p]=[1,2,3] means product p appears in orders 1, 2 and 3
        for o in self.orders:
            for p in o.prods:
                prodSequence[p].append(o.id)

        for p in prodSequence:
            for i in range(len(prodSequence[p])):
                if (i != len(prodSequence[p]) -1):
                    o = prodSequence[p][i]
                    o1 = prodSequence[p][i+1]
                    x = self.P[o][p]
                    x1 = self.P[o1][p]
                    self.solver.add(x < x1)
                
    def breakRunnerSym(self):
        covered_runners = []
        for r in self.runners:
            for r1 in self.runners:
                if(r.id != r1.id and r.initialPos == r1.initialPos and (r.id not in covered_runners) ):
                    a = self.A[r.id]
                    a1 = self.A[r1.id]
                    self.solver.add(a <= a1)    
                    covered_runners.append(r1.id)

    def encodeConstraints(self):
        #1 - A runner cannot spend less than 50% of the max timespan amongst other runners
        self.runnerPercentages()

        #2 - Runners start at their initial position and can go to any product 
        self.runnerInitialPosition()

        #3 - A runner can only carry one product at a time
        self.runnerOneProductAtATime()
        
        #4 - Only one product arriving to the packaging area at a time
        self.packagingAreaConstraint()

        #5 - A runner takes t_ij time from product i to product j. 
        self.productTransitionsConstraint()

        #6 - A runner can only carry a product if they're active
        self.runnerActiveConstraint()

        #8 - A runner i in prod j at time k that goes to prod j' at time k+stime does not carry any other prod in times ]k, k+stime[  TODO
        self.runnerIsBusyConstraint()

        #9 - A product takes c_j time from the conveyor belt to the packaging area 
        self.conveyorBeltConstraint()

        #10 - Each product j in order o is delivered by exactly one runner TODO 
        self.productDeliveredByOneRunner()

        #11 - Breaking Product Symmetries
        self.breakProductSym()

        #12 - Breaking Runner Symmetries
        self.breakRunnerSym()

        # We want the minimum possible time...
        self.solver.minimize(self.time)
                
    def printOutput(self, model):
        time = 0
        x = dict()
        p = dict()
        a = dict()

        for r in self.runners:
            x[r.id] = dict()

        for o in self.orders:
            p[o.id] = dict()
        
        for m in model.decls():

            if (m.name()[0] == "X"):
                var = m.name().split("_")
                runner = int(var[1])
                order = int(var[2])
                prod = int(var[3])
                if (model[m].as_long() != 0):
                    p[order][prod] = model[m].as_long()
                    #p[order] = {k: v for k,v in sorted(p[order].items(), key = lambda item:item[1])}
                x[runner][(order, prod)] = model[m].as_long()
                x[runner] = {k: v for k,v in sorted(x[runner].items(), key = lambda item:item[1])}

            elif (m.name()[0] == "T"):
                time = model[m].as_long() -1

            '''    
            elif (m.name()[0] == "P"):
                order = int(m.name()[2])
                prod = int(m.name()[4])
                p[order][prod] = model[m].as_long()

            elif (m.name()[0] == "A"):
                var
                runner = int(m.name()[2])
                a[runner] = model[m].as_long()'''
        
        for runner in x:
            output = ""
            n_prods_runner = 0
            for i in x[runner]:
                if x[runner][i] != 0:
                    n_prods_runner+=1
                    output += " " + str(i[1])
            print(str(n_prods_runner) + output)

        for o in self.orders:
            output = ""
            prod_len = len(p[o.id])
            for prod in p[o.id]:
                output+= " " + str(prod) + ":" + str(p[o.id][prod])

            print(str(prod_len) + output)

    def getMaxTimebound(self):
        time = 1
        prevProd = self.runners[0].initialPos
        for o in self.orders:
            for p in self.products:
                if(p.id in o.prods):
                    time += p.beltTime
                    #time += self.shelvesTimes[prevProd-1][p.id-1]
                    prevProd = p.id
        return time

    def getMinTimebound(self):
    
        orders_list = dict()
        min_shelves_time =  []
        belts_time = []

        min_times_total = []

        for i in range(1,self.numProds+1):
            orders_list[i] = 0
            
        for o in self.orders:
            for j in o.prods:
                orders_list[j]+=1

        for st in self.shelvesTimes:
            min_shelves_time.append(min(st))

        for p in self.products:
            belts_time.append(p.beltTime)

        for i in range(self.numProds):
            min_time = 0
            for j in range(orders_list[i+1]):
                min_time+=min_shelves_time[i]
            min_time+=belts_time[i]
            min_times_total.append(min_time)

        return max(min_times_total)
    
if __name__ == '__main__':
    p = Problem(sys.stdin.readlines())
    
    minTime = p.getMinTimebound()
    maxTime = p.getMaxTimebound()
       
    #time = binarySearch([i for i in range(minTime, maxTime+1)], p)

    p.solver = z3.Optimize()
    p.createVariables(minTime, maxTime)
    p.encodeConstraints()
    
    if(p.solver.check() == z3.sat):
        model = p.solver.model()
        p.printOutput(model)

    else: 
        print("UNSAT")