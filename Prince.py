## PRINCE reference implementation
## Original Author: David Tvrdý
## Fork Author: Henk Berendsen
## Last edited: 15.10.2025


## ------------ References ------------- ##
## ----------------------------------------
## [1] Julia Borghoff, Anne Canteaut, Tim Guneysu, Elif Bilge Kavun, Miroslav Knezevic, Lars R. Knudsen, Gregor Leander, Ventzislav Nikov, Christof Paar, Christian Rechberger, Peter Rombouts, Søren S. Thomsen, and Tolga Yalcın.
## PRINCE – A Low-Latency Block Cipher for Pervasive Computing Applications. Advances in Cryptology – ASIACRYPT 2012, pages 208–225, 2012.


## ----------- Instructions ------------ ##
## ----------------------------------------

## This is a reference implementation of PRINCE, as presented in [1].

## Use Test() to check the test vectors (available in [1]).
## Use Encrypt(key, message) or Decrypt(key, message) for encryption/decryption.



## ----------------------------------------------------------------------
## Constants
SBox = [0xb,0xf,0x3,0x2,0xa,0xc,0x9,0x1,0x6,0x7,0x8,0x0,0xe,0x5,0xd,0x4]
InvSBox = [0xb,0x7,0x3,0x2,0xf,0xd,0x8,0x9,0xa,0x6,0x4,0x0,0x5,0xe,0xc,0x1]
RC = [ ## round constants
    [0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
    [0x1, 0x3, 0x1, 0x9, 0x8, 0xa, 0x2, 0xe, 0x0, 0x3, 0x7, 0x0, 0x7, 0x3, 0x4, 0x4],
    [0xa, 0x4, 0x0, 0x9, 0x3, 0x8, 0x2, 0x2, 0x2, 0x9, 0x9, 0xf, 0x3, 0x1, 0xd, 0x0],
    [0x0, 0x8, 0x2, 0xe, 0xf, 0xa, 0x9, 0x8, 0xe, 0xc, 0x4, 0xe, 0x6, 0xc, 0x8, 0x9],
    [0x4, 0x5, 0x2, 0x8, 0x2, 0x1, 0xe, 0x6, 0x3, 0x8, 0xd, 0x0, 0x1, 0x3, 0x7, 0x7],
    [0xb, 0xe, 0x5, 0x4, 0x6, 0x6, 0xc, 0xf, 0x3, 0x4, 0xe, 0x9, 0x0, 0xc, 0x6, 0xc],
    [0x7, 0xe, 0xf, 0x8, 0x4, 0xf, 0x7, 0x8, 0xf, 0xd, 0x9, 0x5, 0x5, 0xc, 0xb, 0x1],
    [0x8, 0x5, 0x8, 0x4, 0x0, 0x8, 0x5, 0x1, 0xf, 0x1, 0xa, 0xc, 0x4, 0x3, 0xa, 0xa],
    [0xc, 0x8, 0x8, 0x2, 0xd, 0x3, 0x2, 0xf, 0x2, 0x5, 0x3, 0x2, 0x3, 0xc, 0x5, 0x4],
    [0x6, 0x4, 0xa, 0x5, 0x1, 0x1, 0x9, 0x5, 0xe, 0x0, 0xe, 0x3, 0x6, 0x1, 0x0, 0xd],
    [0xd, 0x3, 0xb, 0x5, 0xa, 0x3, 0x9, 0x9, 0xc, 0xa, 0x0, 0xc, 0x2, 0x3, 0x9, 0x9],
    [0xc, 0x0, 0xa, 0xc, 0x2, 0x9, 0xb, 0x7, 0xc, 0x9, 0x7, 0xc, 0x5, 0x0, 0xd, 0xd]
]

## ----------------------------------------------------------------------
## Auxiliary functions
def AddRoundConst(number, A):
    for i in range(16): A[i] = A[i] ^ RC[number][i]
    return A


def AddKey(A, K):
    for i in range(16): A[i] = A[i] ^ K[i]
    return A


def SBoxLayer(A):
    for i in range(16): A[i] = SBox[A[i]]
    return A
    

def InvSBoxLayer(A):  
    for i in range(16): A[i] = InvSBox[A[i]]
    return A


def MPrimeLayer(A):    
    T = []
    for i in range(16): T.append(0x0)
    for i in range(2):                
        T[0 + 12 * i] = ((A[1 + 12 * i] ^ A[2 + 12 * i] ^ A[3 + 12 * i]) & 0x8) + ((A[0 + 12 * i] ^ A[2 + 12 * i] ^ A[3 + 12 * i]) & 0x4) + ((A[0 + 12 * i] ^ A[1 + 12 * i] ^ A[3 + 12 * i]) & 0x2) + ((A[0 + 12 * i] ^ A[1 + 12 * i] ^ A[2 + 12 * i]) & 0x1)

        T[1 + 12 * i] = ((A[0 + 12 * i] ^ A[1 + 12 * i] ^ A[2 + 12 * i]) & 0x8) + ((A[1 + 12 * i] ^ A[2 + 12 * i] ^ A[3 + 12 * i]) & 0x4) + ((A[0 + 12 * i] ^ A[2 + 12 * i] ^ A[3 + 12 * i]) & 0x2) + ((A[0 + 12 * i] ^ A[1 + 12 * i] ^ A[3 + 12 * i]) & 0x1)

        T[2 + 12 * i] = ((A[0 + 12 * i] ^ A[1 + 12 * i] ^ A[3 + 12 * i]) & 0x8) + ((A[0 + 12 * i] ^ A[1 + 12 * i] ^ A[2 + 12 * i]) & 0x4) + ((A[1 + 12 * i] ^ A[2 + 12 * i] ^ A[3 + 12 * i]) & 0x2) + ((A[0 + 12 * i] ^ A[2 + 12 * i] ^ A[3 + 12 * i]) & 0x1)

        T[3 + 12 * i] = ((A[0 + 12 * i] ^ A[2 + 12 * i] ^ A[3 + 12 * i]) & 0x8) + ((A[0 + 12 * i] ^ A[1 + 12 * i] ^ A[3 + 12 * i]) & 0x4) + ((A[0 + 12 * i] ^ A[1 + 12 * i] ^ A[2 + 12 * i]) & 0x2) + ((A[1 + 12 * i] ^ A[2 + 12 * i] ^ A[3 + 12 * i]) & 0x1)                        
            
        T[4 + 4 * i] = ((A[4 + 4 * i] ^ A[5 + 4 * i] ^ A[6 + 4 * i]) & 0x8) + ((A[5 + 4 * i] ^ A[6 + 4 * i] ^ A[7 + 4 * i]) & 0x4) + ((A[4 + 4 * i] ^ A[6 + 4 * i] ^ A[7 + 4 * i]) & 0x2) + ((A[4 + 4 * i] ^ A[5 + 4 * i] ^ A[7 + 4 * i]) & 0x1)

        T[5 + 4 * i] = ((A[4 + 4 * i] ^ A[5 + 4 * i] ^ A[7 + 4 * i]) & 0x8) + ((A[4 + 4 * i] ^ A[5 + 4 * i] ^ A[6 + 4 * i]) & 0x4) + ((A[5 + 4 * i] ^ A[6 + 4 * i] ^ A[7 + 4 * i]) & 0x2) + ((A[4 + 4 * i] ^ A[6 + 4 * i] ^ A[7 + 4 * i]) & 0x1)

        T[6 + 4 * i] = ((A[4 + 4 * i] ^ A[6 + 4 * i] ^ A[7 + 4 * i]) & 0x8) + ((A[4 + 4 * i] ^ A[5 + 4 * i] ^ A[7 + 4 * i]) & 0x4) + ((A[4 + 4 * i] ^ A[5 + 4 * i] ^ A[6 + 4 * i]) & 0x2) + ((A[5 + 4 * i] ^ A[6 + 4 * i] ^ A[7 + 4 * i]) & 0x1)

        T[7 + 4 * i] = ((A[5 + 4 * i] ^ A[6 + 4 * i] ^ A[7 + 4 * i]) & 0x8) + ((A[4 + 4 * i] ^ A[6 + 4 * i] ^ A[7 + 4 * i]) & 0x4) + ((A[4 + 4 * i] ^ A[5 + 4 * i] ^ A[7 + 4 * i]) & 0x2) + ((A[4 + 4 * i] ^ A[5 + 4 * i] ^ A[6 + 4 * i]) & 0x1)              
    
    for i in range(16): A[i] = T[i]
    return A


def ShiftRows(A):        
    temp = A[1]
    for i in range(3): A[1 + 4*i] = A[5 + 4*i]
    A[13] = temp
    
    temp = A[2]
    A[2] = A[10]
    A[10] = temp
    temp = A[6]
    A[6] = A[14]
    A[14] = temp
    
    temp = A[15]
    for i in range(3): A[15 - 4*i] = A[11 - 4*i]
    A[3] = temp        
    return A
    

def InvShiftRows(A):
    temp = A[13]
    for i in range(3): A[13 - 4*i] = A[9 - 4*i]
    A[1] = temp
    
    temp = A[2]
    A[2] = A[10]
    A[10] = temp
    temp = A[6]
    A[6] = A[14]
    A[14] = temp
    
    temp = A[3]
    for i in range(3): A[3 + 4*i] = A[7 + 4*i]
    A[15] = temp        
    return A


def MLayer(A):
    A = MPrimeLayer(A)
    A = ShiftRows(A)
    return A   


def InvMLayer(A):
    A = InvShiftRows(A)
    A = MPrimeLayer(A)
    return A


def Round(number, A, K):    
    A = SBoxLayer(A)
    A = MLayer(A)
    A = AddRoundConst(number, A)
    A = AddKey(A, K) 
    return A


def InvRound(number, A, K):
    A = AddKey(A, K) 
    A = AddRoundConst(number, A)        
    A = InvMLayer(A)
    A = InvSBoxLayer(A) 
    return A


def CreateNibbles(message, key):       
    A = []
    K = [] 

    for i in range(16):
        a = (message >> (60 - i * 4)) & 0xf
        k = (key >> (60 - i * 4)) & 0xf
        A.append(a)
        K.append(k)
    return A, K


def IntegerFromNibbles(A):
    ciphertext = 0x0
    for i in range(16):
        ciphertext = ciphertext ^ A[i]
        if i != 15: ciphertext = ciphertext << 4
    return ciphertext

## ----------------------------------------------------------------------
## Message as a 64-bit integer, key as a 64-bit integer.
def PrinceCore(key, message):
    ## internal state and the key matrix 
    A, K = CreateNibbles(message, key)
     
    ## key addition
    A = AddKey(A, K)
    
    ## the first round constant
    A = AddRoundConst(0, A)    
    
    ## forward rounds
    for i in range(5): A = Round(i+1, A, K)
       
    ## the middle part  
    A = SBoxLayer(A)    
    A = MPrimeLayer(A)    
    A = InvSBoxLayer(A)
        
    ## backward rounds
    for i in range(5): A = InvRound(i+6, A, K)
        
    ## the last round constant
    A = AddRoundConst(11, A)
    
    ## key addition
    A = AddKey(A, K)    
        
    ## integer from nibbles   
    ciphertext = IntegerFromNibbles(A)      
    
    return ciphertext


## ----------------------------------------------------------------------
## Key as [key_0,key_1] - both 64-bit integers.
def KeySchedule(key):
    k = key[0]
    
    ## ror k_0, 1
    temp_a = (k >> 1) | ((k & 0b1) << 63)
    temp_b = (k >> 63)
    
    k_prime = temp_a ^ temp_b
    
    return k_prime


## ----------------------------------------------------------------------
## Message as a 64-bit integer, key as [key_0,key_1] - both 64-bit integers.
def Encrypt(key, message):
    
    key_extended = KeySchedule(key)
    
    x = key[0] ^ message
    y = PrinceCore(key[1], x)
    z = key_extended ^ y
       
    return z


## ----------------------------------------------------------------------
## Message as a 64-bit integer, key as [key_0,key_1] - both 64-bit integers.
def Decrypt(key, message):
    alpha = 0xc0ac29b7c97c50dd

    key_extended = KeySchedule(key)
    
    x = key_extended ^ message
    y = PrinceCore(key[1] ^ alpha, x)
    z = key[0] ^ y
    
    return z   


## ----------------------------------------------------------------------
## Test vectors and correctness check.

def Test():
  ## test vectors
  print(hex(Encrypt([0x0,0x0],0x0))) ##0x818665aa0d02dfda
  print(hex(Encrypt([0x0,0x0],0xffffffffffffffff))) ##0x604ae6ca03c20ada
  print(hex(Encrypt([0x0,0xffffffffffffffff],0x0))) ##0x78a54cbe737bb7ef
  print(hex(Encrypt([0xffffffffffffffff,0x0],0x0))) ##0x9fb51935fc3df524

  ## correctness
  print(hex(Decrypt([0x0,0x0],Encrypt([0x0,0x0],0x0))))
  print(hex(Decrypt([0x0,0x0],Encrypt([0x0,0x0],0xffffffffffffffff))))
  print(hex(Decrypt([0x0,0xfedcba9876543210],Encrypt([0x0,0xfedcba9876543210],0x0123456789abcdef))))
