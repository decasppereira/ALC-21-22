from model import *
import sys



class Problem:
    def __init__(self, lines):
        self.numRunners = lines[0].rstrip()
        print(self.numRunners)


if __name__ == '__main__':
    p = Problem(sys.stdin)