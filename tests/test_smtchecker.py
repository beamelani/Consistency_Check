import unittest

from stl_consistency.smtchecker import smt_check_consistency
from stl_consistency.parser import STLParser

class TestSMTChecker(unittest.TestCase):

    def make_test(self, formula, result):
        parser = STLParser()
        parsed_formula = parser.parse_formula_as_stl_list(formula)
        self.assertEqual(smt_check_consistency(parsed_formula, False), result)

    def test_and(self):
        self.make_test("a && b", True)

    def test_globally0(self):
        self.make_test("G[2,5] (x > 5 || x < 0)", True)
        

if __name__ == '__main__':
    unittest.main()
