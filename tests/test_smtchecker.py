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

from stl_consistency.smtchecker import smt_check_consistency
from stl_consistency.parser import STLParser

class TestSMTChecker(unittest.TestCase):

    def make_test(self, formula, result):
        parser = STLParser()
        parsed_formula = parser.parse_formula_as_stl_list(formula)
        # print(parsed_formula)
        self.assertEqual(smt_check_consistency(parsed_formula, True), result)

    def test_and(self):
        self.make_test("a && b", True)

    def test_bool(self):
        self.make_test("a && b || c && d && e", True)

    def test_globally0(self):
        self.make_test("G[2,5] (x > 5 || x < 0)", True)

    def test_globally_add(self):
        self.make_test("G[2,5] (x + y > 5 && x - y < 0)", True)

    def test_globally_add_many(self):
        self.make_test("G[2,5] (x + y - z + x > 5 && x - y < 0)", True)
        

if __name__ == '__main__':
    unittest.main()
