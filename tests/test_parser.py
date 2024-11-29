import unittest

from stl_consistency.parser import STLParser
from stl_consistency.node import Node

class TestSTLParser(unittest.TestCase):

    def test_UTerms(self):
        formula = "(y>6) U[3,7] (y < 3)"
        parser = STLParser()
        self.assertEqual(parser.parse_formula_as_stl_list(formula), ['U', '3', '7', ['R_y > 6'], ['R_y < 3']])
        

if __name__ == '__main__':
    unittest.main()
