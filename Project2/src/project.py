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

        self.solver = z3.Solver()

    def createVariables(self, maxTime):
        self.X = dict()
        self.P = dict()
        self.A = dict()

        for i in range(1, self.numRunners+1):
            self.X[i] = dict()
            for o in self.orders:
                self.X[i][o.id] = dict()
                for p in o.prods:
                    self.X[i][o.id][p] = z3.Int("X_%s_%s_%s" %(i, o.id, p))


        for o in self.orders:
            self.P[o.id] = dict()
            for p in o.prods:
                self.P[o.id][p] = z3.Int("P_%s_%s" %(o.id, p))

        for r in range(1, self.numRunners+1):
            self.A[r] = list()
            for t in range(maxTime):
                self.A[r].append(z3.Bool("A_%s_%s" %(r,t)))

    def runnerPercentages(self, maxTime):
        #1 - A runner cannot spend less than 50% of the max timespan amongst other runners
        for r in self.runners:
            for t in range(maxTime):
                for r2 in self.runners:         #TODO this can be moved to the loop below
                    if(r2.id != r.id):
                        self.solver.add_clause([-self.A[r.id][t], self.A[r2.id][math.ceil(t/2)]])

    def runnerInitialTimesActive(self, maxTime):
        for r in self.runners:
            l1 = self.A[r.id][0]
            self.solver.add_clause([l1])

            literals = []
            for j in self.products:
                stime = self.shelvesTimes[r.initialPos-1][j.id-1]
                if(stime < maxTime):
                    literals.append(self.X[r.id][j.id][stime])

                #If a runner goes to prod j at time stime, then it does not carry any other product in times [0, k+stime[
                for j1 in self.products:
                    for t in range(1, stime):
                        if(stime < maxTime):
                            self.solver.add_clause([-self.X[r.id][j.id][stime], -self.X[r.id][j1.id][t]])           
            
            enc = CardEnc.equals(literals, bound = 1, top_id = self.topLit, encoding=EncType.pairwise)
            if len(enc.clauses) > 0:
                self.topLit = max([self.topLit] + [max(c) for c in enc.clauses if len(c) > 0])
            for c in enc.clauses:
                c.append(-l1)
                self.solver.add_clause(c)
        

            for t in range(1, maxTime):      
                #A runner can only be active at t if it was active at t-1
                self.solver.add_clause([-self.A[r.id][t], self.A[r.id][t-1]]) 

            for t in range(maxTime-1):
                #A runner that is innactive at t will be inactive at t+1
                self.solver.add_clause([self.A[r.id][t], -self.A[r.id][t+1]])

    def orderConstraint(self):
        for p in self.products:
            qty = self.productInventory[p.id]
            enc = CardEnc.equals(self.P[p.id][1:], bound = qty, top_id = self.topLit)
            if len(enc.clauses) > 0:
                    self.topLit = max([self.topLit] + [max(c) for c in enc.clauses if len(c) > 0])
            for clause in enc.clauses:
                self.solver.add_clause(clause) 

    def packagingAreaConstraint(self, maxTime):
        for k in range(1, maxTime):
            literals = [p[k] for p in self.P.values()]
            enc = CardEnc.atmost(literals, bound = 1, top_id = self.topLit, encoding=EncType.pairwise)
            if len(enc.clauses) > 0:
                    self.topLit = max([self.topLit] + [max(c) for c in enc.clauses if len(c) > 0])
            for clause in enc.clauses:
                self.solver.add_clause(clause)
           
    def conveyorBeltConstraint(self, maxTime):
        for r in self.runners:
            for j in self.products:
                for k in range(1, maxTime):
                    if (k+j.beltTime) < maxTime:
                        self.solver.add_clause([-self.X[r.id][j.id][k], self.P[j.id][k+j.beltTime]])
                    else:
                        self.solver.add_clause([-self.X[r.id][j.id][k]]) #TODO check this condition

    def runnerOneProductAtATime(self, maxTime):
        for r in self.runners:
            for k in range(maxTime):
                literals = [p[k] for p in self.X[r.id].values()]
                enc = CardEnc.atmost(literals, bound = 1, top_id=self.topLit, encoding=EncType.pairwise)
                for clause in enc.clauses:
                    self.solver.add_clause(clause)

    def runnerIsBusyConstraint(self, maxTime):
        for r in self.runners:
            for j in self.products:
                for k in range(maxTime):
                    l1 = self.X[r.id][j.id][k]

                    for j1 in self.products:
                        time = self.shelvesTimes[j.id-1][j1.id-1]
                        if (k+time) < maxTime:
                            l2 = self.X[r.id][j1.id][k+time]
                            lits = []
                            for t in range(k+1, k+time):
                                for p in self.products:
                                    lits.append(self.X[r.id][p.id][t]) 
                            for l in lits:
                                #self.printClause([-l1, -l2, -l])
                                self.solver.add_clause([-l1, -l2, -l])

    def productTransitionsConstraint(self, maxTime):
        for r in self.runners:
            for j in self.products:
                for k in range(maxTime):
                    l1 = self.X[r.id][j.id][k]
                    literals = []
                    for j1 in self.products:
                        time = self.shelvesTimes[j.id-1][j1.id-1]
                        if (k+time) < maxTime:
                            l2 = self.X[r.id][j1.id][k+time]
                            literals.append(l2)
                    
                    #6 - A runner can also stop being active
                    if (k+1) < maxTime:
                        literals.append(-self.A[r.id][k+1])

                    if(len(literals) > 0):
                        enc = CardEnc.equals(literals, top_id = self.topLit, encoding=EncType.pairwise)
                        if len(enc.clauses) > 0:
                                self.topLit = max([self.topLit] + [max(c) for c in enc.clauses if len(c) > 0])
                        for c in enc.clauses:
                            c.append(-l1)
                            self.solver.add_clause(c)
                   
                   
                    #7 - A runner can only carry a product if they're active
                    self.solver.add_clause([-l1, self.A[r.id][k]])

    def productArrivingPackaging(self, maxTime):
        for p in self.products:
            for k in range(maxTime):
                if(k-p.beltTime > 0):
                    l = self.P[p.id][k]
                    runnerLits = [self.X[i][p.id][k-p.beltTime] for i in range(1, self.numRunners+1)]
                    enc = CardEnc.equals(runnerLits, bound = 1, top_id = self.topLit, encoding=EncType.pairwise)
                    for c in enc.clauses:
                        c.append(-l)
                        self.solver.add_clause(c)
                else:
                    self.solver.add_clause([-self.P[p.id][k]])

    def encodeConstraints(self, maxTime):
        #1 - A runner cannot spend less than 50% of the max timespan amongst other runners
        self.runnerPercentages(maxTime)

        #2 - Runners start at time 0 in product j and never take breaks
        self.runnerInitialTimesActive(maxTime)

        #3 - All products from all orders must arrive to the packaging area 
        self.orderConstraint()
        
        #4 - Only one product arriving to the packaging area at a time
        self.packagingAreaConstraint(maxTime)

        #5 - A runner takes t_ij time from product i to product j.
        self.productTransitionsConstraint(maxTime)

        #8 - A runner i in prod j at time k that goes to prod j' at time k+stime does not carry any other prod in times ]k, k+stime[  
        self.runnerIsBusyConstraint(maxTime)

        #9 - A product takes c_j time from the conveyor belt to the packaging area
        self.conveyorBeltConstraint(maxTime)

        #10 - A runner can only carry one product at a time
        self.runnerOneProductAtATime(maxTime)

        #11 - If a product arrives to the packaging area, it was only placed by one runner
        self.productArrivingPackaging(maxTime)
                
    def printOutput(self, model, timebound):
        print(timebound-1)
        usedProducts = []

        runnerProds=dict().fromkeys([i for i in range(1, self.numRunners+1)])
        for i in runnerProds:
            runnerProds[i] = []

        orders = dict().fromkeys([i for i in range(1, self.numOrders+1)])
        for o in self.orders:
            orders[o.id] = dict()
            for p in o.prods:
                orders[o.id][p] = -1

        for v in model:
            if abs(v) in self.translate_X:
                if(v > 0):
                    r = self.translate_X[v][0]
                    j = self.translate_X[v][1]
                    k = self.translate_X[v][2]
                    #print("{} ".format(v), end="")
                    #print((r, j, k))
                    runnerProds[r].append((j, k))
                    for o in self.orders:
                        if (j in o.prods) and (orders[o.id][j] == -1 ):
                            orders[o.id][j] = k
                            break
            else:
                break
        
        for r in runnerProds:
            print("{} ".format(len(runnerProds[r])), end="")
            runnerProds[r].sort(key = lambda x:x[1])
            for p in runnerProds[r]:
                print("{} ".format(p[0]), end="")
            print()

        for o in orders:
            print("{} ".format(len(orders[o])), end="")
            for p in orders[o]:
                 print("{}:{} ".format(p, orders[o][p]), end="")
            print()

    def printModel(self, model):
        for v in model:
            if (abs(v) in self.translate_X) and (v>0):
                i = self.translate_X[v][0]
                j = self.translate_X[v][1]
                k = self.translate_X[v][2] 
                print("Runner {} with prod {} at time {}".format(i, j, k))
            elif (abs(v) in self.translate_P) and (v>0):
                j = self.translate_P[v][0]
                k = self.translate_P[v][1]
                print("Product {} arriving at time {}".format(j, k))
            elif (abs(v) in self.translate_A) and (v>0):
                i = self.translate_A[v][0]
                k = self.translate_A[v][1] 
                print("Runner {} active at time {}".format(i,  k))

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
    
   

def binarySearch(possibleTimes, p):
    if (len(possibleTimes) == 1): #Found solution
        return possibleTimes[0]

    elif (len(possibleTimes) == 2):
        return possibleTimes[1]

    else:
        midPos = len(possibleTimes)//2
        timebound = possibleTimes[midPos]

        p.solver = Glucose4()
        p.createVariables(timebound)
        p.encodeConstraints(timebound)
    
        if(p.solver.solve()):
            model = p.solver.get_model()
            possibleTimes = [i for i in range(possibleTimes[0], timebound+1)]
            return binarySearch(possibleTimes, p)

        else:
            possibleTimes = [i for i in range(timebound +1, possibleTimes[len(possibleTimes)-1]+1)]
            return binarySearch(possibleTimes, p)
        
def linearSearch(min, max, p):
    timebound = minTime
    foundSol = False

    for timebound in range(minTime, maxTime):
        p.solver = Glucose4()
        p.createVariables(timebound)
        p.encodeConstraints(timebound)
    
        if(p.solver.solve()):
            foundSol = True
            break
            
    if (foundSol):
        model = p.solver.get_model()
        p.printOutput(model, timebound)
    else:
        print("UNSAT")


if __name__ == '__main__':
    p = Problem(sys.stdin.readlines())
    
    minTime = p.getMinTimebound()
    #maxTime = p.getMaxTimebound()
    time = 9
       
    #time = binarySearch([i for i in range(minTime, maxTime+1)], p)

    p.solver = z3.Solver()
    p.createVariables(time)
    print(p.X)
    print(p.P)
    print(p.A)
    '''p.encodeConstraints(time)

    if (p.solver.solve()):
        model = p.solver.get_model()
        p.printOutput(model, time)
    else:
        print("UNSAT")'''
   


    