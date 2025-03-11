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

from stl_consistency.tableau import make_tableau
from stl_consistency.parser import STLParser

class TestTableau(unittest.TestCase):

    def make_test(self, formula, max_depth, expected, mltl=False):
        parser = STLParser()
        parsed_formula = parser.parse_formula_as_node(formula)
        #print(parser.parse_formula_as_stl_list(formula))
        res = make_tableau(parsed_formula, max_depth, 'sat', False, False, False, mltl)
        self.assertEqual(res, expected)

    def test_and(self):
        self.make_test("a && b", 5, True)

    def test_many_ops(self):
        self.make_test("a && b && c && (a || b || c) && d", 5, True)

    def test_true(self):
        self.make_test("a && !TrUe", 5, False)

    def test_false(self):
        self.make_test("a && FaLsE", 5, False)

    def test_globally0(self):
        self.make_test("G[2,5] (R_x > 5 || R_x < 0)", 10, True)
        
    def test_globally_add(self):
        self.make_test("G[2,5] (R_x + R_y > 5 && R_x - R_y < 0)", 10, True)

    def test_globally_add_many(self):
        self.make_test("G[2,5] (R_x + R_y - R_z + R_x > 5 && R_x - R_y < 0)", 10, True)
    
    def test_release(self):
        self.make_test("(R_x == 10) R[1,6] (R_x < 10)", 10, True)

    def test_abs(self):
        self.make_test("G[0,5] (|x| > 20 | |x| < 10) && F[0,5] (x == -15)", 20, False)

    def test_mltl(self):
        formula = "F[58,92] ((a1) U[87,100] ((a1 && a0 && ! a1) U[9,100] (a0)))"
        self.make_test(formula, 200, False, mltl=False)
        self.make_test(formula, 200, True, mltl=True)

    def test_release(self):
        self.make_test("false R[0,10] a", 100, True)

if __name__ == '__main__':
    unittest.main()
