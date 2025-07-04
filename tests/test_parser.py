# MIT License
#
# Copyright (c) 2024 Ezio Bartocci, Michele Chiari, Beatrice Melani
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

import unittest

from stl_consistency.parser import STLParser
from stl_consistency.node import Node

class TestSTLParser(unittest.TestCase):

    def test_UTerms(self):
        formula = "(y>6) U[3,7] (y < 3)"
        parser = STLParser()
        self.assertEqual(parser.parse_formula_as_stl_list(formula), ['U', '3', '7', ['>', 'y', '6'], ['<', 'y', '3']])
        
    def test_int_expr(self):
        formula = "G[0,5] (x - y <= x + z + 5 && z + y > 42)"
        parser = STLParser()
        self.assertEqual(
            parser.parse_formula_as_stl_list(formula),
            ['G', '0', '5', ['&&', ['<=', ['-', 'x', 'y'], ['+', ['+', 'x', 'z'], '5']], ['>', ['+', 'z', 'y'], '42']]]
        )

    def test_iff(self):
        formula = "G[0,5] (x - y <= x + z + 5 <-> z + y > 42)"
        parser = STLParser()
        self.assertEqual(
            parser.parse_formula_as_stl_list(formula),
            ['G', '0', '5', [
                '||',
                ['&&', ['<=', ['-', 'x', 'y'], ['+', ['+', 'x', 'z'], '5']], ['>', ['+', 'z', 'y'], '42']],
                ['&&', ['!', ['<=', ['-', 'x', 'y'], ['+', ['+', 'x', 'z'], '5']]], ['!', ['>', ['+', 'z', 'y'], '42']]]
            ]]
        )

    def test_parens(self):
        formula = "G[0,5] (x - (y + z) == 0)"
        parser = STLParser()
        self.assertEqual(
            parser.parse_formula_as_stl_list(formula),
            ['G', '0', '5', ['==', ['-', 'x', ['+', 'y', 'z']], '0']]
        )

    def test_abs(self):
        formula = "G[0,5] (|x| > 20 | |x| < 10)"
        parser = STLParser()
        self.assertEqual(
            parser.parse_formula_as_stl_list(formula),
            ['G', '0', '5', ['||', ['>', ['abs', 'x'], '20'], ['<', ['abs', 'x'], '10']]]
        )

if __name__ == '__main__':
    unittest.main()
