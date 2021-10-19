# BEGIN termcolor package

# coding: utf-8
# Copyright (c) 2008-2011 Volvox Development Team
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.
#
# Author: Konstantin Lepa <konstantin.lepa@gmail.com>

"""ANSII Color formatting for output in terminal."""

from __future__ import print_function

import itertools
import math
import os

__ALL__ = ['colored', 'cprint']

VERSION = (1, 1, 0)

ATTRIBUTES = dict(
    list(zip([
        'bold',
        'dark',
        '',
        'underline',
        'blink',
        '',
        'reverse',
        'concealed'
    ],
        list(range(1, 9))
    ))
)
del ATTRIBUTES['']

HIGHLIGHTS = dict(
    list(zip([
        'on_grey',
        'on_red',
        'on_green',
        'on_yellow',
        'on_blue',
        'on_magenta',
        'on_cyan',
        'on_white'
    ],
        list(range(40, 48))
    ))
)

COLORS = dict(
    list(zip([
        'grey',
        'red',
        'green',
        'yellow',
        'blue',
        'magenta',
        'cyan',
        'white',
    ],
        list(range(30, 38))
    ))
)

RESET = '\033[0m'


def colored(text, color=None, on_color=None, attrs=None):
    """Colorize text.

    Available text colors:
        red, green, yellow, blue, magenta, cyan, white.

    Available text highlights:
        on_red, on_green, on_yellow, on_blue, on_magenta, on_cyan, on_white.

    Available attributes:
        bold, dark, underline, blink, reverse, concealed.

    Example:
        colored('Hello, World!', 'red', 'on_grey', ['blue', 'blink'])
        colored('Hello, World!', 'green')
    """
    if os.getenv('ANSI_COLORS_DISABLED') is None:
        fmt_str = '\033[%dm%s'
        if color is not None:
            text = fmt_str % (COLORS[color], text)

        if on_color is not None:
            text = fmt_str % (HIGHLIGHTS[on_color], text)

        if attrs is not None:
            for attr in attrs:
                text = fmt_str % (ATTRIBUTES[attr], text)

        text += RESET
    return text


def cprint(text, color=None, on_color=None, attrs=None, **kwargs):
    """Print colorize text.

    It accepts arguments of print function.
    """

    print((colored(text, color, on_color, attrs)), **kwargs)


# END termcolor package


import argparse
from typing import IO

runner_colors = ['red', 'green', 'yellow', 'blue', 'magenta', 'cyan', 'white']


def round_up_to_even(f):
    return math.ceil(f / 2.) * 2


class IncorrectFormat(Exception): pass


class WPS:

    def __init__(self, fp: IO):
        try:
            self.n_runners = int(fp.readline())
        except:
            raise IncorrectFormat('Error while reading number of runners from instance file.')

        try:
            self.m_products = int(fp.readline())
        except:
            raise IncorrectFormat('Error while reading number of products from instance file.')

        try:
            self.initial_positions = list(map(int, fp.readline().split()))
        except:
            raise IncorrectFormat('Error while reading initial runner positions from instance file.')

        try:
            self.move_times = []
            for i in range(self.m_products):
                self.move_times.append(list(map(int, fp.readline().split())))
        except:
            raise IncorrectFormat('Error while reading move times between products from instance file.')

        try:
            self.travel_times = list(map(int, fp.readline().split()))
        except:
            raise IncorrectFormat('Error while reading the travel times for each product from instance file.')

        try:
            self.o_orders = int(fp.readline())
        except:
            raise IncorrectFormat('Error while reading number of orders from instance file.')

        try:
            self.orders = []
            for i in range(self.o_orders):
                self.orders.append(list(map(int, fp.readline().split()))[1:])
        except:
            raise IncorrectFormat('Error while reading orders from instance file.')

        self.product_orders_number = [0] * self.m_products
        self.product_orders_mapping = [[] for i in range(self.m_products)]
        for order_i, order in enumerate(self.orders):
            for product in order:
                self.product_orders_number[product - 1] += 1
                self.product_orders_mapping[product - 1].append(order_i)

    def read_solution(self, fp):
        try:
            self.max_timespan = int(fp.readline())
        except:
            raise IncorrectFormat('Error while reading max timespan from solution file.')

        try:
            self.runner_product = []
            for i in range(self.n_runners):
                self.runner_product.append(list(map(int, fp.readline().split()))[1:])
        except:
            raise IncorrectFormat('Error while reading which products are handled by which runners from solution file.')

        try:
            self.order_times = []
            for i in range(self.o_orders):
                self.order_times.append({int(elem[0]): int(elem[1]) for elem in map(lambda x: x.split(':'), fp.readline().split()[1:])})
        except:
            raise IncorrectFormat('Error while reading the times at which product was placed in the conveyors from solution file.')

    def print_visualization(self):
        true_max_span = 0
        for order in self.order_times:
            for product, time in order.items():
                true_max_span = max(true_max_span, self.travel_times[product - 1] + time)

        if true_max_span != self.max_timespan:
            print('WARNING: max span is incorrectly calculated...')

        first_column_width = max(map(len, map(lambda x: f'Runner {x + 1}', range(self.n_runners))))
        first_column_width = max(first_column_width, max(map(len, map(lambda x: f'Product {x + 1}', range(self.m_products)))))
        first_column_width += 2

        time_cell_width = round_up_to_even(max(2 + len(str(true_max_span + 1)), len(f'p{self.m_products + 1}_{self.o_orders + 1}')))
        time_cell_spacer = '⎸'.ljust(time_cell_width, ' ')

        for i in range(self.n_runners):
            print(f'Runner {i + 1}'.ljust(first_column_width, ' '), end='')

            current_pos = self.initial_positions[i]
            current_time = 0
            for elem, color in zip(self.runner_product[i], itertools.cycle(runner_colors)):
                w = self.move_times[current_pos - 1][elem - 1]

                if len(f'p{current_pos}→p{elem}') + 2 <= time_cell_width * w:
                    string = f'p{current_pos}→p{elem}'
                else:
                    string = f'p{elem}'

                print(colored(string.center(time_cell_width * w), color=color, attrs=['reverse']), end='')
                current_pos = elem
                current_time += w

            print(time_cell_spacer * (true_max_span + 1 - current_time))

        print((' ' * first_column_width) + time_cell_spacer * (true_max_span + 1))

        for product_i in range(self.m_products):
            print(f'Product {product_i + 1}'.ljust(first_column_width, ' '), end='')

            first = True

            if len(self.product_orders_mapping[product_i]) == 0:
                print(time_cell_spacer * (true_max_span + 1))

            for order_i, color in zip(self.product_orders_mapping[product_i], itertools.cycle(runner_colors)):
                if not first:
                    print(' ' * first_column_width, end='')
                first = False

                print(time_cell_spacer * self.order_times[order_i][product_i + 1], end='')
                print(colored(f'p{product_i + 1}_{order_i + 1}'.center(time_cell_width * self.travel_times[product_i]), color=color, attrs=['reverse']), end='')
                print(time_cell_spacer * (true_max_span + 1 - self.order_times[order_i][product_i + 1] - self.travel_times[product_i]), end='')

                print()

        print(' ' * first_column_width, end='')
        for i in range(true_max_span + 1):
            print(str(i).ljust(time_cell_width, ' '), end='')

        print()


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Scheduling visualizer for the WPS problem.')

    parser.add_argument('INSTANCE', help='instance file')
    parser.add_argument('SOLUTION', help='solution file containing the scheduling')

    args = parser.parse_args()

    with open(args.INSTANCE) as f:
        wps = WPS(f)

    with open(args.SOLUTION) as f:
        wps.read_solution(f)

    wps.print_visualization()
