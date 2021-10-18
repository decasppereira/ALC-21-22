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