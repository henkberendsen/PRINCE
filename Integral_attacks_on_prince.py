## Integral attacks on round reduced version of PRINCE
## Author: David Tvrdý
## Last edited: 25.03.2022



## ------------ References ------------- ##
## ----------------------------------------
## [1] Julia Borghoff, Anne Canteaut, Tim Guneysu, Elif Bilge Kavun, Miroslav Knezevic, Lars R. Knudsen, Gregor Leander, Ventzislav Nikov, Christof Paar, Christian Rechberger, Peter Rombouts, Søren S. Thomsen, and Tolga Yalcın.
## PRINCE – A Low-Latency Block Cipher for Pervasive Computing Applications. Advances in Cryptology – ASIACRYPT 2012, pages 208–225, 2012.
## [2] P. Morawiecki. Practical attacks on the round-reduced PRINCE. IACR Cryptol. ePrint Arch., 2015:245, 2017.
## [3] Raluca Posteuca and Gabriel Negara. Integral cryptanalysis of round-reduced PRINCE cipher. 
## Proceedings of the Romanian Academy - Series A: Mathematics, Physics, Technical Sciences, Information Science, 16:265–269, 01 2015.
## [4] S. Rasoolzadeh and H. Raddum. Faster key recovery attack on round-reduced PRINCE. 
## In Andrey Bogdanov, editor, Lightweight Cryptography for Security and Privacy - 5th International Workshop, LightSec 2016, Aksaray, Turkey, September 21-22, 2016, Revised Selected Papers, volume 10098 of Lecture Notes in Computer Science, pages 3–17. Springer, 2016.



## ----------- Instructions ------------ ##
## ----------------------------------------

## This is an implementation of several integral attacks on round reduced versions of PRINCE (see [1]) as they were described in the original papers [2],[3] and [4].

## The first section handles the reference implementation of PRINCE.
## Each one of the remaining sections provides one attack on round reduced version of PRINCE.
## Square4BasicSingle(secret_key) ... A basic attack on 4-round reduced version of PRINCE. Recovers one nibble of the key (k'_0 ^ k_1).
## Square4BasicFull(secret_key) ... A basic attack on 4-round reduced version of PRINCE. Recovers the whole key k_0, k_1.
## Square4ArraysFull(secret_key) ... An advanced attack on 4-round reduced version of PRINCE which uses the faster key recovery technique. Recovers the whole key k_0, k_1.
## Square5ArraysFull(secret_key)... An advanced attack on 5-round reduced version of PRINCE which uses the faster key recovery technique. Recovers the whole key k_0, k_1.







## ------------- PART ONE -------------- ##
## PRINCE reference implementation
## ----------------------------------------





import math
## ----------------------------------------------------------------------
## Message as a 64-bit integer, key as a 64-bit integer.
def PrinceCore(key, message, rounds):
    
    SBox = [0xb,0xf,0x3,0x2,0xa,0xc,0x9,0x1,0x6,0x7,0x8,0x0,0xe,0x5,0xd,0x4]
    InvSBox = [0xb,0x7,0x3,0x2,0xf,0xd,0x8,0x9,0xa,0x6,0x4,0x0,0x5,0xe,0xc,0x1]

    ## round constants
    RC = [
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

    ## auxiliary functions 
    
    def AddRoundConst(number):
        for i in range(16): A[i] = A[i] ^ RC[number][i]
        return  
    
    
    def AddKey():
        for i in range(16): A[i] = A[i] ^ K[i]
        return  


    def SBoxLayer():
        for i in range(16): A[i] = SBox[A[i]]
        return       
        

    def InvSBoxLayer():  
        for i in range(16): A[i] = InvSBox[A[i]]
        return  

    
    def MPrimeLayer():    
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
        return 
    

    def ShiftRows():        
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
        return 
      

    def InvShiftRows():
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
        return 
    

    def MLayer():
        MPrimeLayer()
        ShiftRows()
        return    
 

    def InvMLayer():
        InvShiftRows()
        MPrimeLayer()
        return 
    
    
    def Round(number):    
        SBoxLayer()
        MLayer()
        AddRoundConst(number)
        AddKey() 
        return  
    

    def InvRound(number):
        AddKey() 
        AddRoundConst(number)        
        InvMLayer()
        InvSBoxLayer() 
        return 
    

    def CreateNibbles():
      for i in range(16):
        a = (message >> (60 - i * 4)) & 0xf
        k = (key >> (60 - i * 4)) & 0xf
        A.append(a)
        K.append(k)
      return


    def IntegerFromNibbles(A):
      ciphertext = 0x0
      for i in range(16):
        ciphertext = ciphertext ^ A[i]
        if i != 15: ciphertext = ciphertext << 4
      return ciphertext



    ## -------------------------------------------
    ## internal state and the key matrix        
    A = []
    K = []  
  
    CreateNibbles()
        
    ## key addition
    AddKey()
    
    ## the first round constant
    AddRoundConst(0)    
    
    ## forward rounds
    
    for i in range(math.ceil((rounds - 2)/2)): Round(i+1)
       
    ## the middle part  
    SBoxLayer()    
    MPrimeLayer()    
    InvSBoxLayer()
        
    ## backward rounds
    for i in range(math.floor((rounds - 2)/2)): InvRound(i + 1 + math.ceil((rounds - 2)/2) + 12 - rounds)
        
    ## the last round constant
    AddRoundConst(11)
    
    ## key addition
    AddKey()    
        
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
def Encrypt(key, message, rounds):
    
    key_extended = KeySchedule(key)
    
    x = key[0] ^ message
    y = PrinceCore(key[1], x, rounds)
    z = key_extended ^ y
       
    return z

## ----------------------------------------------------------------------
## Message as a 64-bit integer, key as [key_0,key_1] - both 64-bit integers.
def Decrypt(key, message):
    alpha = 0xc0ac29b7c97c50dd

    key_extended = KeySchedule(key)
    
    x = key_extended ^ message
    y = PrinceCore(key[1] ^ alpha, x, 12)
    z = key[0] ^ y
    
    return z   


## ----------------------------------------------------------------------
## Test vectors and correctness check.

def Test():
  ## test vectors
  print(hex(Encrypt([0x0,0x0],0x0, 12))) ##0x818665aa0d02dfda
  print(hex(Encrypt([0x0,0x0],0xffffffffffffffff, 12))) ##0x604ae6ca03c20ada
  print(hex(Encrypt([0x0,0xffffffffffffffff],0x0, 12))) ##0x78a54cbe737bb7ef
  print(hex(Encrypt([0xffffffffffffffff,0x0],0x0, 12))) ##0x9fb51935fc3df524

  ## correctness
  print(hex(Decrypt([0x0,0x0],Encrypt([0x0,0x0],0x0, 12))))
  print(hex(Decrypt([0x0,0x0],Encrypt([0x0,0x0],0xffffffffffffffff, 12))))
  print(hex(Decrypt([0x0,0xfedcba9876543210],Encrypt([0x0,0xfedcba9876543210],0x0123456789abcdef, 12))))










import random
import time
## ------------- SECTION TWO -------------- ##
## Integral attacks on round-reduced Prince: 4 Rounds, Basic Version
## ----------------------------------------












## ----------------------------------------------------------------------
## -------------------- four rounds square attack ------------------------
## -- basic version, one nibble of k0'^k1 recovery --

def Square4BasicSingle(secret_key):
    
    SBox = [0xb,0xf,0x3,0x2,0xa,0xc,0x9,0x1,0x6,0x7,0x8,0x0,0xe,0x5,0xd,0x4]
    InvSBox = [0xb,0x7,0x3,0x2,0xf,0xd,0x8,0x9,0xa,0x6,0x4,0x0,0x5,0xe,0xc,0x1]
    ## round constants
    RC = [
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

    rounds = 4    
    extended_key = KeySchedule(secret_key)
    print('4 round basic square attack - last nibble of key recovery')
    print('Target key :', hex(extended_key ^ secret_key[1]))
    print('-----------------------')
    
    start = time.time()

    ## one if the index is a candidate for the key
    key_candidates = [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
    
    ## number of remaining key candidates
    key_count = 16

    ## a constant for creating PT pairs
    const = random.randint(0x0, 0xfffffffffffffff)
    
    while key_count > 1:
        
        const += 1
        if const > 0xfffffffffffffff: const = 0

        ## create PT sets
        pt = []
        for i in range(16): pt.append( (const << 4) + i )
        
        ## encrypt
        ct = []
        for i in range(16): ct.append( Encrypt(secret_key, pt[i], rounds) )

        ## guess a nibble of (k0' ^ k1) .... the last nibble implemented  
        for k in range(16):
            if key_candidates[k] == 1:
                ## patrially decrypt all ciphertexts and check the XOR property
                s = 0
                for i in range(16): s ^= SBox[(ct[i] & 0xf) ^ k ^ RC[11][15]]
                    
                if s == 0: print('Key candidate', hex(k))
                else: 
                    key_candidates[k] = 0
                    key_count -= 1

        print(key_count,'key candidates left\n-----------------------') 
        
    end = time.time()

    for i in range(16): 
        if key_candidates[i] == 1: 
            print('Key :',hex(i))

    print('Run time:', end - start)  








## ------------- SECTION THREE -------------- ##
## Integral attacks on round-reduced Prince: 4 Rounds, Basic Version, Full key
## ----------------------------------------











## ----------------------------------------------------------------------
## -------------------- four rounds square attack ------------------------
## -- basic version, full key recovery
    
def Square4BasicFull(secret_key):
    
    SBox = [0xb,0xf,0x3,0x2,0xa,0xc,0x9,0x1,0x6,0x7,0x8,0x0,0xe,0x5,0xd,0x4]
    InvSBox = [0xb,0x7,0x3,0x2,0xf,0xd,0x8,0x9,0xa,0x6,0x4,0x0,0x5,0xe,0xc,0x1]
    ## round constants
    RC = [
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
    
    rounds = 4    
    extended_key = KeySchedule(secret_key)
    print('4 round basic square attack - full key recovery')
    print('Target key :', hex(secret_key[1] ^ extended_key))
    print('Target key :', hex(secret_key[0]), hex(secret_key[1]))
    print('-----------------------')
    
    start = time.time()
    
    ## S-box operations counter
    s_box_count = 0    
    
    
    #### PART 1 - k0'^k1 recovery ################################
    print('\n************Part one************\n-----------------------')
    
    key_candidates = []
    for i in range(16): key_candidates.append([1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])
    key_count = [16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16]

    const = random.randint(0x0,0xfffffffffffffff)
    ready = False

    while not ready:
        const += 1
        if const > 0xfffffffffffffff: const = 0x0
        
        ## create PT sets
        pt = []
        for i in range(16): pt.append( (const << 4) + i )

        ## encrypt
        ct = []
        for i in range(16): 
            ct.append( Encrypt(secret_key, pt[i], rounds) )
            s_box_count += 16*rounds

        ## guess a nibble of (k0' ^ k1) .... all nibbles
        for nibble in range(16):
            if key_count[nibble] > 1:
                for k in range(16):
                    if key_candidates[nibble][k] == 1:
                        ## patrially decrypt all ciphertexts and check the XOR property
                        s = 0
                        for i in range(16): 
                            s ^= SBox[((ct[i] & (0xf << 4*(15 - nibble))) >> 4*(15 - nibble)) ^ k ^ RC[11][nibble]]
                            s_box_count += 1
                            
                        if s == 0: print('Key candidate', hex(k), 'of nibble', nibble)
                        else: 
                            key_candidates[nibble][k] = 0
                            key_count[nibble] -= 1

        ready = True
        for i in range(16):
            if key_count[i] > 1: 
                ready = False
                break

        if not ready: print('several key candidates left\n-----------------------') 
        
    end = time.time()
    final_key_last = 0x0
    for nibble in range(16):
        for i in range(16): 
            if key_candidates[nibble][i] == 1: 
                final_key_last = (final_key_last << 4) + i
    print('Recovered key - last round key :', hex(final_key_last))
    print('Run time:', end - start)  
    print('S Box Count :', s_box_count)
    
    
    #### PART 2 - k1 recovery ######################################
    print('\n************Part two************\n-----------------------')
    
    key_candidates = []
    for i in range(16): key_candidates.append([1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])
    key_count = [16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16]
    
    const = random.randint(0x0,0xff)
    ready = False

    while not ready:
        const += 1
        if const > 0xff: const = 0x0
        ## create PT sets
        
        pt = []       
        for i in range(16): pt.append( (i << (15*4)) + (i << (8*4)) + (i << (5*4)) + (i << (2*4)) + const )
                                  
                                
        ## encrypt
        ct = []
        
        for i in range(16):
            ## peel of the last round
            
            temp_c = Encrypt(secret_key, pt[i], rounds)     
            s_box_count += 16*rounds
            temp_c ^= final_key_last    
            
            A = [] 
            ## create nibbles    
            for j in range(16):
                a = (temp_c >> (60 - j * 4)) & 0xf               
                A.append(a)
                
            ## round constant and S-layer   
            for j in range(16): A[j] = A[j] ^ RC[11][j]
            for j in range(16): A[j] = SBox[A[j]] 
            s_box_count += 16
            
            ## MPrime    
            T = []
            for j in range(16): T.append(0x0)
            for j in range(2):                
                T[0 + 12 * j] = ((A[1 + 12 * j] ^ A[2 + 12 * j] ^ A[3 + 12 * j]) & 0x8) + ((A[0 + 12 * j] ^ A[2 + 12 * j] ^ A[3 + 12 * j]) & 0x4) + ((A[0 + 12 * j] ^ A[1 + 12 * j] ^ A[3 + 12 * j]) & 0x2) + ((A[0 + 12 * j] ^ A[1 + 12 * j] ^ A[2 + 12 * j]) & 0x1)
                T[1 + 12 * j] = ((A[0 + 12 * j] ^ A[1 + 12 * j] ^ A[2 + 12 * j]) & 0x8) + ((A[1 + 12 * j] ^ A[2 + 12 * j] ^ A[3 + 12 * j]) & 0x4) + ((A[0 + 12 * j] ^ A[2 + 12 * j] ^ A[3 + 12 * j]) & 0x2) + ((A[0 + 12 * j] ^ A[1 + 12 * j] ^ A[3 + 12 * j]) & 0x1)
                T[2 + 12 * j] = ((A[0 + 12 * j] ^ A[1 + 12 * j] ^ A[3 + 12 * j]) & 0x8) + ((A[0 + 12 * j] ^ A[1 + 12 * j] ^ A[2 + 12 * j]) & 0x4) + ((A[1 + 12 * j] ^ A[2 + 12 * j] ^ A[3 + 12 * j]) & 0x2) + ((A[0 + 12 * j] ^ A[2 + 12 * j] ^ A[3 + 12 * j]) & 0x1)
                T[3 + 12 * j] = ((A[0 + 12 * j] ^ A[2 + 12 * j] ^ A[3 + 12 * j]) & 0x8) + ((A[0 + 12 * j] ^ A[1 + 12 * j] ^ A[3 + 12 * j]) & 0x4) + ((A[0 + 12 * j] ^ A[1 + 12 * j] ^ A[2 + 12 * j]) & 0x2) + ((A[1 + 12 * j] ^ A[2 + 12 * j] ^ A[3 + 12 * j]) & 0x1)                        
                T[4 + 4 * j] = ((A[4 + 4 * j] ^ A[5 + 4 * j] ^ A[6 + 4 * j]) & 0x8) + ((A[5 + 4 * j] ^ A[6 + 4 * j] ^ A[7 + 4 * j]) & 0x4) + ((A[4 + 4 * j] ^ A[6 + 4 * j] ^ A[7 + 4 * j]) & 0x2) + ((A[4 + 4 * j] ^ A[5 + 4 * j] ^ A[7 + 4 * j]) & 0x1)
                T[5 + 4 * j] = ((A[4 + 4 * j] ^ A[5 + 4 * j] ^ A[7 + 4 * j]) & 0x8) + ((A[4 + 4 * j] ^ A[5 + 4 * j] ^ A[6 + 4 * j]) & 0x4) + ((A[5 + 4 * j] ^ A[6 + 4 * j] ^ A[7 + 4 * j]) & 0x2) + ((A[4 + 4 * j] ^ A[6 + 4 * j] ^ A[7 + 4 * j]) & 0x1)
                T[6 + 4 * j] = ((A[4 + 4 * j] ^ A[6 + 4 * j] ^ A[7 + 4 * j]) & 0x8) + ((A[4 + 4 * j] ^ A[5 + 4 * j] ^ A[7 + 4 * j]) & 0x4) + ((A[4 + 4 * j] ^ A[5 + 4 * j] ^ A[6 + 4 * j]) & 0x2) + ((A[5 + 4 * j] ^ A[6 + 4 * j] ^ A[7 + 4 * j]) & 0x1)
                T[7 + 4 * j] = ((A[5 + 4 * j] ^ A[6 + 4 * j] ^ A[7 + 4 * j]) & 0x8) + ((A[4 + 4 * j] ^ A[6 + 4 * j] ^ A[7 + 4 * j]) & 0x4) + ((A[4 + 4 * j] ^ A[5 + 4 * j] ^ A[7 + 4 * j]) & 0x2) + ((A[4 + 4 * j] ^ A[5 + 4 * j] ^ A[6 + 4 * j]) & 0x1)              
            for i in range(16): A[i] = T[i]
                
            ## shift rows 
            temp = A[1]
            for j in range(3): A[1 + 4*j] = A[5 + 4*j]
            A[13] = temp
            temp = A[2]
            A[2] = A[10]
            A[10] = temp
            temp = A[6]
            A[6] = A[14]
            A[14] = temp
            temp = A[15]
            for j in range(3): A[15 - 4*j] = A[11 - 4*j]
            A[3] = temp   
            
            ## round constant and S-layer   
            for j in range(16): A[j] = A[j] ^ RC[10][j]
                
            ## integer from nibbles   
            ciphertext = 0x0
            for j in range(16):
                ciphertext = ciphertext ^ A[j]
                if j != 15: ciphertext = ciphertext << 4
            
            ct.append(ciphertext)
           
            
            
        ## guess a nibble of (k1) .... all nibbles
        for nibble in range(16):
            if key_count[nibble] > 1:
                for k in range(16):
                    if key_candidates[nibble][k] == 1:
                        ## patrially decrypt all ciphertexts and check the XOR property
                        s = 0
                        for i in range(16): 
                            s ^= SBox[((ct[i] & (0xf << 4*(15 - nibble))) >> 4*(15 - nibble)) ^ k]
                            s_box_count += 1
                            
                        if s == 0: print('Key candidate', hex(k), 'of nibble', nibble)
                        else: 
                            key_candidates[nibble][k] = 0
                            key_count[nibble] -= 1

        ready = True
        for i in range(16):
            if key_count[i] > 1: 
                ready = False
                break

        if not ready: print('several key candidates left\n-----------------------') 
        
    end = time.time()
    final_key_1 = 0x0
    for nibble in range(16):
        for i in range(16): 
            if key_candidates[nibble][i] == 1: 
                final_key_1 = (final_key_1 << 4) + i
    print('Recovered key - k1 :', hex(final_key_1))
    print('Run time:', end - start)      
    print('S Box Count :', s_box_count)
    
    #### PART 3 - k0 recovery ######################################
    print('\n************Part three************\n-----------------------')
    final_key_extended = final_key_last ^ final_key_1
    bit_high = final_key_extended >> 63
    bit_xor = (final_key_extended >> 62) & 0x1
    final_key_0 = (((final_key_extended << 1) + bit_high) ^ (bit_xor << 1)) & 0xffffffffffffffff
    end = time.time()
        
    print('Recovered key - k0 :', hex(final_key_0))
    print('-----------------------')
    print('Target key :', hex(secret_key[0]), hex(secret_key[1]))
    print('Recovered key :', hex(final_key_0), hex(final_key_1))

    print('Run time:', end - start)  
    print('S Box Count :', s_box_count)








## ------------- SECTION FOUR -------------- ##
## Integral attacks on round-reduced Prince: 4 Rounds, Faster key recovery Version, Full key
## ----------------------------------------










## ----------------------------------------------------------------------
## -------------------- four rounds square attack ------------------------
## -- version using arrays instead of ciphertexts, full key recovery


def Square4ArraysFull(secret_key):
    
    SBox = [0xb,0xf,0x3,0x2,0xa,0xc,0x9,0x1,0x6,0x7,0x8,0x0,0xe,0x5,0xd,0x4]
    InvSBox = [0xb,0x7,0x3,0x2,0xf,0xd,0x8,0x9,0xa,0x6,0x4,0x0,0x5,0xe,0xc,0x1]
    ## round constants
    RC = [
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
  
    rounds = 4    
    extended_key = KeySchedule(secret_key)
    print('4 round square attack with arrays - full key recovery')
    print('Target key :', hex(secret_key[1] ^ extended_key))
    print('Target key :', hex(secret_key[0]), hex(secret_key[1]))
    print('-----------------------')
    
    start = time.time()
    s_box_count = 0
        
    
    #### PART 1 - k0'^k1 recovery ################################
    print('\n************Part one************\n-----------------------')
    
    key_candidates = []
    A_array = []
    for i in range(16): key_candidates.append([1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])
    key_count = [16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16]
    for i in range(16): A_array.append([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])

    const = random.randint(0x0,0xfffffffffffffff)
    ready = False

    while not ready:
        const += 1
        if const > 0xfffffffffffffff: const = 0x0
        
        ## create PT sets        
        for i in range(16): 
            pt = (const << 4) + i 

            ## encrypt PTs and flip the corresponding bit in the A-array
            ct = Encrypt(secret_key, pt, rounds)
            s_box_count += 16*rounds
            
            for j in range(16):
                flip = (ct >> 4*(15 - j)) & 0xf
                A_array[j][flip] ^= 1

        ## guess a nibble of (k0' ^ k1) .... all nibbles
        for nibble in range(16):
            if key_count[nibble] > 1:
                for k in range(16):
                    if key_candidates[nibble][k] == 1:
                        ## patrially decrypt all ciphertexts and check the XOR property
                        s = 0
                        for i in range(16):
                            if A_array[nibble][i] == 1:
                                s ^= SBox[i ^ k ^ RC[11][nibble]]
                                s_box_count += 1
                                
                        if s == 0: print('Key candidate', hex(k), 'of nibble', nibble)
                        else: 
                            key_candidates[nibble][k] = 0
                            key_count[nibble] -= 1

        ready = True
        for i in range(16):
            if key_count[i] > 1: 
                ready = False
                break

        if not ready: print('several key candidates left\n-----------------------') 
        
    end = time.time()
    final_key_last = 0x0
    
    for nibble in range(16):
        for i in range(16): 
            if key_candidates[nibble][i] == 1: 
                final_key_last = (final_key_last << 4) + i
                
    print('Recovered key - last round key :', hex(final_key_last))
    print('Run time:', end - start) 
    print('S Box Count :', s_box_count)
    
    
    #### PART 2 - k1 recovery ######################################
    print('\n************Part two************\n-----------------------')
    
    key_candidates = []
    A_array = []
    for i in range(16): key_candidates.append([1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])
    key_count = [16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16]
    for i in range(16): A_array.append([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])
    
    const = random.randint(0x0,0xff)
    ready = False

    while not ready:
        const += 1
        if const > 0xff: const = 0x00
            
        ## create PT sets              
        for i in range(16): 
            pt = (i << (15*4)) + (i << (8*4)) + (i << (5*4)) + (i << (2*4)) + const
                    
            ## encrypt      
            temp_c = Encrypt(secret_key, pt, rounds)  
            s_box_count += 16*rounds
            
            
            ## peel of the last round
            temp_c ^= final_key_last    
            
            A = [] 
            
            ## create nibbles    
            for j in range(16):
                a = (temp_c >> (60 - j * 4)) & 0xf               
                A.append(a)
                
            ## round constant and S-layer   
            for j in range(16): A[j] = A[j] ^ RC[11][j]
            for j in range(16): A[j] = SBox[A[j]] 
            s_box_count += 16
            
            ## MPrime    
            T = []
            for j in range(16): T.append(0x0)
            for j in range(2):                
                T[0 + 12 * j] = ((A[1 + 12 * j] ^ A[2 + 12 * j] ^ A[3 + 12 * j]) & 0x8) + ((A[0 + 12 * j] ^ A[2 + 12 * j] ^ A[3 + 12 * j]) & 0x4) + ((A[0 + 12 * j] ^ A[1 + 12 * j] ^ A[3 + 12 * j]) & 0x2) + ((A[0 + 12 * j] ^ A[1 + 12 * j] ^ A[2 + 12 * j]) & 0x1)
                T[1 + 12 * j] = ((A[0 + 12 * j] ^ A[1 + 12 * j] ^ A[2 + 12 * j]) & 0x8) + ((A[1 + 12 * j] ^ A[2 + 12 * j] ^ A[3 + 12 * j]) & 0x4) + ((A[0 + 12 * j] ^ A[2 + 12 * j] ^ A[3 + 12 * j]) & 0x2) + ((A[0 + 12 * j] ^ A[1 + 12 * j] ^ A[3 + 12 * j]) & 0x1)
                T[2 + 12 * j] = ((A[0 + 12 * j] ^ A[1 + 12 * j] ^ A[3 + 12 * j]) & 0x8) + ((A[0 + 12 * j] ^ A[1 + 12 * j] ^ A[2 + 12 * j]) & 0x4) + ((A[1 + 12 * j] ^ A[2 + 12 * j] ^ A[3 + 12 * j]) & 0x2) + ((A[0 + 12 * j] ^ A[2 + 12 * j] ^ A[3 + 12 * j]) & 0x1)
                T[3 + 12 * j] = ((A[0 + 12 * j] ^ A[2 + 12 * j] ^ A[3 + 12 * j]) & 0x8) + ((A[0 + 12 * j] ^ A[1 + 12 * j] ^ A[3 + 12 * j]) & 0x4) + ((A[0 + 12 * j] ^ A[1 + 12 * j] ^ A[2 + 12 * j]) & 0x2) + ((A[1 + 12 * j] ^ A[2 + 12 * j] ^ A[3 + 12 * j]) & 0x1)                        
                T[4 + 4 * j] = ((A[4 + 4 * j] ^ A[5 + 4 * j] ^ A[6 + 4 * j]) & 0x8) + ((A[5 + 4 * j] ^ A[6 + 4 * j] ^ A[7 + 4 * j]) & 0x4) + ((A[4 + 4 * j] ^ A[6 + 4 * j] ^ A[7 + 4 * j]) & 0x2) + ((A[4 + 4 * j] ^ A[5 + 4 * j] ^ A[7 + 4 * j]) & 0x1)
                T[5 + 4 * j] = ((A[4 + 4 * j] ^ A[5 + 4 * j] ^ A[7 + 4 * j]) & 0x8) + ((A[4 + 4 * j] ^ A[5 + 4 * j] ^ A[6 + 4 * j]) & 0x4) + ((A[5 + 4 * j] ^ A[6 + 4 * j] ^ A[7 + 4 * j]) & 0x2) + ((A[4 + 4 * j] ^ A[6 + 4 * j] ^ A[7 + 4 * j]) & 0x1)
                T[6 + 4 * j] = ((A[4 + 4 * j] ^ A[6 + 4 * j] ^ A[7 + 4 * j]) & 0x8) + ((A[4 + 4 * j] ^ A[5 + 4 * j] ^ A[7 + 4 * j]) & 0x4) + ((A[4 + 4 * j] ^ A[5 + 4 * j] ^ A[6 + 4 * j]) & 0x2) + ((A[5 + 4 * j] ^ A[6 + 4 * j] ^ A[7 + 4 * j]) & 0x1)
                T[7 + 4 * j] = ((A[5 + 4 * j] ^ A[6 + 4 * j] ^ A[7 + 4 * j]) & 0x8) + ((A[4 + 4 * j] ^ A[6 + 4 * j] ^ A[7 + 4 * j]) & 0x4) + ((A[4 + 4 * j] ^ A[5 + 4 * j] ^ A[7 + 4 * j]) & 0x2) + ((A[4 + 4 * j] ^ A[5 + 4 * j] ^ A[6 + 4 * j]) & 0x1)              
            for i in range(16): A[i] = T[i]
                
            ## shift rows 
            temp = A[1]
            for j in range(3): A[1 + 4*j] = A[5 + 4*j]
            A[13] = temp
            temp = A[2]
            A[2] = A[10]
            A[10] = temp
            temp = A[6]
            A[6] = A[14]
            A[14] = temp
            temp = A[15]
            for j in range(3): A[15 - 4*j] = A[11 - 4*j]
            A[3] = temp        
            
            ## round constant and S-layer   
            for j in range(16): A[j] = A[j] ^ RC[10][j]    
                
            ## flip the corresponding A_array bit
            for j in range(16): A_array[j][A[j]] ^= 1
            

        ## guess a nibble of (k1) .... all nibbles
        for nibble in range(16):
            if key_count[nibble] > 1:
                for k in range(16):
                    if key_candidates[nibble][k] == 1:
                        ## patrially decrypt all ciphertexts and check the XOR property
                        s = 0
                        for i in range(16):
                            if A_array[nibble][i] == 1:
                                s ^= SBox[i ^ k]
                                s_box_count += 1
                                
                        if s == 0: print('Key candidate', hex(k), 'of nibble', nibble)
                        else: 
                            key_candidates[nibble][k] = 0
                            key_count[nibble] -= 1

        ready = True
        for i in range(16):
            if key_count[i] > 1: 
                ready = False
                break

        if not ready: print('several key candidates left\n-----------------------') 
        
    end = time.time()
    final_key_1 = 0x0
    
    for nibble in range(16):
        for i in range(16): 
            if key_candidates[nibble][i] == 1: 
                final_key_1 = (final_key_1 << 4) + i
                
    print('Recovered key - k1 :', hex(final_key_1))
    print('Run time:', end - start)      
    print('S Box Count :', s_box_count)
    
    #### PART 3 - k0 recovery ######################################
    print('\n************Part three************\n-----------------------')
    final_key_extended = final_key_last ^ final_key_1
    bit_high = final_key_extended >> 63
    bit_xor = (final_key_extended >> 62) & 0x1
    final_key_0 = (((final_key_extended << 1) + bit_high) ^ (bit_xor << 1)) & 0xffffffffffffffff
    end = time.time()
        
    print('Recovered key - k0 :', hex(final_key_0))
    print('-----------------------')
    print('Target key :', hex(secret_key[0]), hex(secret_key[1]))
    print('Recovered key :', hex(final_key_0), hex(final_key_1))

    print('Run time:', end - start)  
    print('S Box Count :', s_box_count)











## ------------- SECTION FIVE -------------- ##
## Integral attacks on round-reduced Prince: 5 Rounds, Faster key recovery Version, Full key
## ----------------------------------------











## ----------------------------------------------------------------------
## -------------------- five round square attack ------------------------
## -- version using arrays instead of ciphertexts, full key recovery


def Square5ArraysFull(secret_key):
    
    SBox = [0xb,0xf,0x3,0x2,0xa,0xc,0x9,0x1,0x6,0x7,0x8,0x0,0xe,0x5,0xd,0x4]
    InvSBox = [0xb,0x7,0x3,0x2,0xf,0xd,0x8,0x9,0xa,0x6,0x4,0x0,0x5,0xe,0xc,0x1]
    ## round constants
    RC = [
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
    
    rounds = 5  
    extended_key = KeySchedule(secret_key)
    print('5 round square attack with arrays - full key recovery')
    print('Target key :', hex(secret_key[1] ^ extended_key))
    print('Target key :', hex(secret_key[0]), hex(secret_key[1]))
    print('-----------------------')
    
    start = time.time()
    s_box_count = 0
        
    
    #### PART 1 - k0'^k1 recovery ################################
    print('\n************Part one************\n-----------------------')
    
    key_candidates = []
    A_array = []
    for i in range(16): key_candidates.append([1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])
    key_count = [16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16]
    for i in range(16): A_array.append([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])

    const = random.randint(0x0,0xfffffffffff)
    ready = False

    while not ready:
        const += 1
        if const > 0xfffffffffff: const = 0x0
        ## create PT sets
        
        for i in range(2**12): 
          pt = (const << 12) + i
            
          ## encrypt the PTs and flip the corresponding bit of the A-array
          ct = Encrypt(secret_key, pt, rounds)
          s_box_count += 16*rounds
          
          for j in range(16):
              flip = (ct >> 4*(15 - j)) & 0xf
              A_array[j][flip] ^= 1

        ## guess a nibble of (k0' ^ k1) .... all nibbles
        for nibble in range(16):
            if key_count[nibble] > 1:
                for k in range(16):
                    if key_candidates[nibble][k] == 1:
                        ## patrially decrypt all ciphertexts and check the XOR property
                        s = 0
                        for i in range(16):
                            if A_array[nibble][i] == 1:
                                s ^= SBox[i ^ k ^ RC[11][nibble]]
                                s_box_count += 1
                                
                        if s == 0: print('Key candidate', hex(k), 'of nibble', nibble)
                        else: 
                            key_candidates[nibble][k] = 0
                            key_count[nibble] -= 1

        ready = True
        for i in range(16):
            if key_count[i] > 1: 
                ready = False
                break

        if not ready: print('several key candidates left\n-----------------------') 
        
    end = time.time()
    final_key_last = 0x0
    
    for nibble in range(16):
        for i in range(16): 
            if key_candidates[nibble][i] == 1: 
                final_key_last = (final_key_last << 4) + i
                
    print('Recovered key - last round key :', hex(final_key_last))
    print('Run time:', end - start) 
    print('S Box Count :', s_box_count)
    
    
    #### PART 2 - k1 recovery ######################################
    print('\n************Part two************\n-----------------------')
    
    key_candidates = []
    A_array = []
    for i in range(16): key_candidates.append([1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])
    key_count = [16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16]
    for i in range(16): A_array.append([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])
    
    const = random.randint(0x0,0xfffffffffffffff)
    ready = False

    while not ready:
        const += 1  
        if const > 0xfffffffffffffff: const = 0x0      
        ## create PT sets
        
        for i in range(16): 
          pt = (const << 4) + i
        
          ## encrypt
          temp_c = Encrypt(secret_key, pt, rounds)  
          s_box_count += 16*rounds
          
          
          ## peel of the last round
          temp_c ^= final_key_last    
          
          A = [] 
          
          ## create nibbles    
          for j in range(16):
              a = (temp_c >> (60 - j * 4)) & 0xf               
              A.append(a)
              
          ## round constant and S-layer   
          for j in range(16): A[j] = A[j] ^ RC[11][j]
          for j in range(16): A[j] = SBox[A[j]] 
          s_box_count += 16
          
          ## MPrime    
          T = []
          for j in range(16): T.append(0x0)
          for j in range(2):                
              T[0 + 12 * j] = ((A[1 + 12 * j] ^ A[2 + 12 * j] ^ A[3 + 12 * j]) & 0x8) + ((A[0 + 12 * j] ^ A[2 + 12 * j] ^ A[3 + 12 * j]) & 0x4) + ((A[0 + 12 * j] ^ A[1 + 12 * j] ^ A[3 + 12 * j]) & 0x2) + ((A[0 + 12 * j] ^ A[1 + 12 * j] ^ A[2 + 12 * j]) & 0x1)
              T[1 + 12 * j] = ((A[0 + 12 * j] ^ A[1 + 12 * j] ^ A[2 + 12 * j]) & 0x8) + ((A[1 + 12 * j] ^ A[2 + 12 * j] ^ A[3 + 12 * j]) & 0x4) + ((A[0 + 12 * j] ^ A[2 + 12 * j] ^ A[3 + 12 * j]) & 0x2) + ((A[0 + 12 * j] ^ A[1 + 12 * j] ^ A[3 + 12 * j]) & 0x1)
              T[2 + 12 * j] = ((A[0 + 12 * j] ^ A[1 + 12 * j] ^ A[3 + 12 * j]) & 0x8) + ((A[0 + 12 * j] ^ A[1 + 12 * j] ^ A[2 + 12 * j]) & 0x4) + ((A[1 + 12 * j] ^ A[2 + 12 * j] ^ A[3 + 12 * j]) & 0x2) + ((A[0 + 12 * j] ^ A[2 + 12 * j] ^ A[3 + 12 * j]) & 0x1)
              T[3 + 12 * j] = ((A[0 + 12 * j] ^ A[2 + 12 * j] ^ A[3 + 12 * j]) & 0x8) + ((A[0 + 12 * j] ^ A[1 + 12 * j] ^ A[3 + 12 * j]) & 0x4) + ((A[0 + 12 * j] ^ A[1 + 12 * j] ^ A[2 + 12 * j]) & 0x2) + ((A[1 + 12 * j] ^ A[2 + 12 * j] ^ A[3 + 12 * j]) & 0x1)                        
              T[4 + 4 * j] = ((A[4 + 4 * j] ^ A[5 + 4 * j] ^ A[6 + 4 * j]) & 0x8) + ((A[5 + 4 * j] ^ A[6 + 4 * j] ^ A[7 + 4 * j]) & 0x4) + ((A[4 + 4 * j] ^ A[6 + 4 * j] ^ A[7 + 4 * j]) & 0x2) + ((A[4 + 4 * j] ^ A[5 + 4 * j] ^ A[7 + 4 * j]) & 0x1)
              T[5 + 4 * j] = ((A[4 + 4 * j] ^ A[5 + 4 * j] ^ A[7 + 4 * j]) & 0x8) + ((A[4 + 4 * j] ^ A[5 + 4 * j] ^ A[6 + 4 * j]) & 0x4) + ((A[5 + 4 * j] ^ A[6 + 4 * j] ^ A[7 + 4 * j]) & 0x2) + ((A[4 + 4 * j] ^ A[6 + 4 * j] ^ A[7 + 4 * j]) & 0x1)
              T[6 + 4 * j] = ((A[4 + 4 * j] ^ A[6 + 4 * j] ^ A[7 + 4 * j]) & 0x8) + ((A[4 + 4 * j] ^ A[5 + 4 * j] ^ A[7 + 4 * j]) & 0x4) + ((A[4 + 4 * j] ^ A[5 + 4 * j] ^ A[6 + 4 * j]) & 0x2) + ((A[5 + 4 * j] ^ A[6 + 4 * j] ^ A[7 + 4 * j]) & 0x1)
              T[7 + 4 * j] = ((A[5 + 4 * j] ^ A[6 + 4 * j] ^ A[7 + 4 * j]) & 0x8) + ((A[4 + 4 * j] ^ A[6 + 4 * j] ^ A[7 + 4 * j]) & 0x4) + ((A[4 + 4 * j] ^ A[5 + 4 * j] ^ A[7 + 4 * j]) & 0x2) + ((A[4 + 4 * j] ^ A[5 + 4 * j] ^ A[6 + 4 * j]) & 0x1)              
          for i in range(16): A[i] = T[i]
              
          ## shift rows 
          temp = A[1]
          for j in range(3): A[1 + 4*j] = A[5 + 4*j]
          A[13] = temp
          temp = A[2]
          A[2] = A[10]
          A[10] = temp
          temp = A[6]
          A[6] = A[14]
          A[14] = temp
          temp = A[15]
          for j in range(3): A[15 - 4*j] = A[11 - 4*j]
          A[3] = temp     
          
          ## round constant and S-layer   
          for j in range(16): A[j] = A[j] ^ RC[10][j]   
              
          ## flip the corresponding A_array bit
          for j in range(16): A_array[j][A[j]] ^= 1
          

        ## guess a nibble of (k1) .... all nibbles
        for nibble in range(16):
            if key_count[nibble] > 1:
                for k in range(16):
                    if key_candidates[nibble][k] == 1:
                        ## patrially decrypt all ciphertexts and check the XOR property                        
                        s = 0
                        for i in range(16):
                            if A_array[nibble][i] == 1:
                                s ^= SBox[i ^ k]
                                s_box_count += 1
                                
                        if s == 0: print('Key candidate', hex(k), 'of nibble', nibble)
                        else: 
                            key_candidates[nibble][k] = 0
                            key_count[nibble] -= 1

        ready = True
        for i in range(16):
            if key_count[i] > 1: 
                ready = False
                break

        if not ready: print('several key candidates left\n-----------------------') 
        
    end = time.time()
    final_key_1 = 0x0
    
    for nibble in range(16):
        for i in range(16): 
            if key_candidates[nibble][i] == 1: 
                final_key_1 = (final_key_1 << 4) + i
                
    print('Recovered key - k1 :', hex(final_key_1))
    print('Run time:', end - start)      
    print('S Box Count :', s_box_count)
    
    
    #### PART 3 - k0 recovery ######################################
    print('\n************Part three************\n-----------------------')
    final_key_extended = final_key_last ^ final_key_1
    bit_high = final_key_extended >> 63
    bit_xor = (final_key_extended >> 62) & 0x1
    final_key_0 = (((final_key_extended << 1) + bit_high) ^ (bit_xor << 1)) & 0xffffffffffffffff
    end = time.time()
        
    print('Recovered key - k0 :', hex(final_key_0))
    print('-----------------------')
    print('Target key :', hex(secret_key[0]), hex(secret_key[1]))
    print('Recovered key :', hex(final_key_0), hex(final_key_1))

    print('Run time:', end - start)  
    print('S Box Count :', s_box_count)












######################################################## TEST
#Square4BasicSingle([random.randint(0x0,0xffffffffffffffff), random.randint(0x0, 0xffffffffffffffff)])
#Square4BasicFull([random.randint(0x0,0xffffffffffffffff), random.randint(0x0,0xffffffffffffffff)])
#Square4ArraysFull([random.randint(0x0,0xffffffffffffffff), random.randint(0x0,0xffffffffffffffff)])
#Square5ArraysFull([random.randint(0x0,0xffffffffffffffff), random.randint(0x0,0xffffffffffffffff)])
