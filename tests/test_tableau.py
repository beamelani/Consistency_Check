import unittest

from stl_consistency.tableau import make_tableau
from stl_consistency.parser import STLParser

class TestTableau(unittest.TestCase):

    def make_test(self, formula, max_depth, expected):
        parser = STLParser()
        parsed_formula = parser.parse_formula_as_node(formula)
        print(parser.parse_formula_as_stl_list(formula))
        _, res = make_tableau(parsed_formula, max_depth, 'sat')
        self.assertEqual(res, expected)

    def test_and(self):
        self.make_test("a && b", 5, True)

    def test_globally0(self):
        self.make_test("G[2,5] (R_x > 5 || R_x < 0)", 10, True)
        

if __name__ == '__main__':
    unittest.main()
