import numpy as np
from functools import reduce
from operator import xor

def pseudo_random_byte_generator(seed=None, bit_generator=None, **kwargs):
    
    if bit_generator is None:
        poly = [12, 6, 4, 1, 0]
        bits = LFSR(poly, seed)
    else:
        bits = bit_generator(seed, **kwargs)
        
    while True:
        outp_byte = sum(int(next(bits))<<i for i in range(8))
        yield outp_byte
        


class LFSR(object):
    '''
    Implementation of an LFSR with iterator
    
    Attributes:
        poly: list of int
            polynomial expressed as a list of int corresponding to
            the degree of non-zero polinomials
            
        state: optional int
            integer representing initial state (default 11...1)
    '''
    
    def __init__(self, poly, state=None):
        self._poly = sum([2**i for i in poly]) >> 1 # p0 always one
        self._length = max(poly)
        
        # If no state provided initialize with 111...1
        self._smask = (1<<self._length) - 1
        if state is None:
            state = self._smask
        self.state = state
        
        self._output = self._state >> (self._length-1)
        
        self._feedback = self._parity(self._state & self._poly)
    
    # Computes the parity bit of a number for XOR in the feedback
    def _parity(self, num):
        ite = 1
        ones = 0
        while ite <= num:
            if ite & num:
                ones = ones + 1
            ite = ite << 1
        return ones % 2
    
    # ==== OUTPUT ====
    @property
    def output(self):
        return self._output
    # No possible to change the output value
    @output.setter
    def output(self, val):
        raise AttributeError('Denied')
        
    # ==== FEEDBACK ====
    @property
    def feedback(self):
        return self._feedback
    @feedback.setter
    def feedback(self, feedback):
        self._feedback = bool(feedback)
        
    # ==== LENGTH ====
    @property
    def length(self):
        return self._length
    @output.setter
    def length(self, val):
        raise AttributeError('Denied')
        
    # ==== STATE ====
    @property
    def state(self):
        # state is re-reversed before being read
        return int(f'{self._state:0{len(self)}b}'[::-1], 2)
    @state.setter
    def state(self, state):
        self._state = int(f'{state:0{len(self)}b}'[::-1], 2)
    
    # For making the iterator
    def __iter__(self):
        return self
    
    def __next__(self):
        '''Execute an LFSR step returning the output bit'''
        self._state = ((self._state << 1) | self._feedback) & self._smask
        self._output = self._state >> (self._length-1)
        self._feedback = self._parity(self._state & self._poly)
        return bool(self._output)
    
    def __len__(self):
        return self._length
    
    def run_steps(self, N=1):
        '''
        Run given number of steps
        
        Parameters:
            N: int >= 1
                desired number of steps to be performed
        
        Return: bool list of length N
        '''
        return [next(self) for _ in range(n)]
    
    def cycle(self, state=None):
        '''
        Execute full cycle of LFSR
        
        Parameters:
            state: optional int
                optionally a different internal state can be set
        
        Return: bool list of length (2**lfsr.length)-1
        '''
        if state is not None:
            self.state = state
        return self.run_steps(2**len(self) - 1)
    
    def __str__(self):
        return None
    
class BerlekampMassey():
    '''
    Class implementing the Berlek-Amp Massey algorithm in
    streaming way.
    
    Call:
        input: bit
            next bit in the LFSR list
    '''
    
    def __init__(self):
        self._bits = 0b0
        
        self._P = 1
        self._m = 0
        self._Q = 1
        self._r = 1
        self._t = 0
    
    def __call__(self, bit):
        self._bits = (self._bits<<1) | int(bit)
        
        d = 0
        for j in range(self._m+1):
            d += ((self._P>>j) & 1) & ((self._bits>>(j)) & 1)
        d = d % 2
        
        if d == 1:
            if 2*self._m <= self._t:
                self._P, self._Q = self._P^(self._Q<<self._r), self._P
                
                self._m = self._t + 1 - self._m
                self._r = 0
                self._bits &= (1<<self._m) - 1
            else:
                self._P = self._P^(self._Q<<self._r)
        
        self._r += 1
        self._t += 1
        return self._P

class StreamCipher():
    '''
    The class implements the provided Pseudo Random Number Generator.
    
    Methods:
        encrypt: Takes the plaintext end return the encoded ciphertext
        
        decrypt: Takes the ciphertext and return the decoded plaintext
    '''
    
    def __init__(self, key, prng=None, **kwargs):
        if prng is None:
            # If not provided use default PRNG
            self._prng = pseudo_random_byte_generator()
        else:
            # If provided call the function
            self._prng = prng(key, **kwargs)
            
    def encrypt(self, plaintext):
        '''Provide a plaintext as a byte string and return
        the encrypted ciphertext.
        Bytes are encoded byte-to-byte.'''
        return bytes(ch ^ next(self._prng) for ch in plaintext)
    
    def decrypt(self, ciphertext):
        '''Provide a ciphertext as a byte string and return
        the decrypted plaintext.
        Bytes are decoded byte-to-byte.'''
        return bytes(ch ^ next(self._prng) for ch in ciphertext)

    
#########################################
##  A5/1 bit generator implementation  ##
#########################################
class A5_1(object):
    '''
    A5/1 stream cipher
    '''
    
    def __init__(self, key, frame=0, debug=False):
        key_length = 64
        frame_length = 22
        polys = [
            [19, 18, 17, 14, 0],
            [22, 21, 0],
            [23, 22, 21, 8, 0]
        ]
        
        self._lfsrs = [LFSR(poly, state=0) for poly in polys]
        self._ckbits = [10, 11, 12]
        self._count = 0
        
        # Initialize LFSR with key
        if debug:
            print("---- KEY INSERTION ----")
            print("LFSR1  LFSR2   LFSR3")
        for bit, i in zip([int(ci) for ci in f'{key:0{key_length}b}'[::-1]], range(key_length)):
            for lfsr in self._lfsrs:
                lfsr.feedback ^= bit
                next(lfsr)
            if debug and (i < 10):
                print(f'{self._lfsrs[0].state:05x}  {self._lfsrs[1].state:06x}  {self._lfsrs[2].state:06x}')
        if debug:
            print("...    ...     ...")
            print(f'{self._lfsrs[0].state:05x}  {self._lfsrs[1].state:06x}  {self._lfsrs[2].state:06x}')
        
        # Add frame to LFSRs
        if debug:
            print("---- FRAME INSERTION ----")
            print("LFSR1  LFSR2   LFSR3")
        for bit in [int(ci) for ci in f'{frame:0{frame_length}b}'[::-1][:frame_length]]:
            for lfsr in self._lfsrs:
                lfsr.feedback ^= bit
                next(lfsr)
            if debug:
                print(f'{self._lfsrs[0].state:05x}  {self._lfsrs[1].state:06x}  {self._lfsrs[2].state:06x}')
        
        if debug:
            print("---- KEY MIXING ----")
        for _ in range(100):
            next(self)
        
    @property
    def majority(self):
        bits = [bool(lfsr.state & (1 << ckbit)) for lfsr, ckbit in zip(self._lfsrs, self._ckbits)]

        majority = sum(bits) > 1
        return majority
    
    @majority.setter
    def majority(self, val):
        raise AttributeError('Denied')
    
    def __iter__(self):
        return self
    
    def __next__(self):
        maj = self.majority
        
        for lfsr, ckbit in zip(self._lfsrs, self._ckbits):
            if bool(lfsr.state & (1<<ckbit)) == maj:
                next(lfsr)
        
        return self.output
    
    # ==== OUTPUT PROPERTY ====
    @property
    def output(self):
        output = reduce(xor, [lfsr.output for lfsr in self._lfsrs])
        return output
    @output.setter
    def output(self, val):
        raise AttributeError('Denied')
    
    # ==== PRINT CURRENT REGISTER STATUS ===
    def __str__(self):
        _str = f'LFSR1: {self._lfsrs[0].state:05x}  LFSR2: {self._lfsrs[1].state:06x}  LFSR3: {self._lfsrs[2].state:06x}  output: {self.output}'
        return _str
    def __repr__(self):
        return f'A5/1 PRNG -> ({str(self)})'

#########################################
##  RC4 byte generator implementation  ##
#########################################
class RC4(object):
    '''
    RC4 Stream Cipher implementation
    '''
    
    def __init__(self, key, key_length=None, drop=0):
        '''
        
        '''
        
        self._L = key_length # Store the key length
        if self._L is None:
            self._L = len(key)
        
        self._i = 0
        self._j = 0
        
        # Generate identity permutation
        self._P = np.array(range(256))
        # Initialize permutation with given key
        for i in range(256):
            self._j = (self._j + self._P[i] + key[i % self._L]) % 256
            self._P[i], self._P[self._j] = self._P[self._j], self._P[i]
        
        self._j = 0
        
        # If drop > 0, discard initial #drop bytes produced
        for _ in range(drop):
            next(self)
    
    def __iter__(self):
        return self
    
    def __next__(self):
        self._i = (self._i + 1) % 256
        self._j = (self._j + self._P[self._i]) % 256
        self._P[self._i], self._P[self._j] = self._P[self._j], self._P[self._i]
        return int(self._P[(self._P[self._i] + self._P[self._j]) % 256])
    
##################################################
##  Useful function to visually print polynome  ##
##################################################
def print_poly(poly):
    '''
    Given a int list representing the power of exponents of
    non zero coeff, represents in visual form x^3 + ...
    '''
    poly = [i for i, b in enumerate(f'{poly:b}'[::-1]) if bool(int(b))]
    poly = ' + '.join([
        (f'x^{d}' if d > 1 else ('x' if d==1 else '1')) 
        for d in poly[::-1]
    ])
    print(poly)