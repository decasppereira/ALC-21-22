class Product:
    def __init__(self, id, order_id):
        self.id = id
        self.order_id = order_id

class Order:
    def __init__(self, id, prods):
        self.id = id
        self.prods = prods

class Runner:
    def __init__(self, id):
        self.id = id
        self.workTime = 0