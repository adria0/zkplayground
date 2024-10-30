import math
from hashlib import blake2b

class Fri:
    def __init__( self, offset, omega, initial_domain_length, expansion_factor, num_colinearity_tests ):
        self.offset = offset
        self.omega = omega
        self.domain_length = initial_domain_length
        self.field = omega.field
        self.expansion_factor = expansion_factor
        self.num_colinearity_tests = num_colinearity_tests

    def num_rounds( self ):
        codeword_length = self.domain_length
        num_rounds = 0
        while codeword_length > self.expansion_factor and 4*self.num_colinearity_tests < codeword_length:
            codeword_length /= 2
            num_rounds += 1
        return num_rounds

    def eval_domain( self ):
        return [self.offset * (self.omega^i) for i in range(self.domain_length)]
    

    