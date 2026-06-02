## PRINCE and PRINCEv2 reference implementation
## Original Author: David Tvrdý
## Fork Author: Henk Berendsen
## Last edited: 02.06.2026


## ------------ References ------------- ##
## [1] Julia Borghoff, Anne Canteaut, Tim Güneysu, Elif Bilge Kavun, Miroslav Knežević, Lars R. Knudsen, Gregor Leander, Ventzislav Nikov, Christof Paar, Christian Rechberger, Peter Rombouts, Søren S. Thomsen, and Tolga Yalçın
##     PRINCE – A Low-Latency Block Cipher for Pervasive Computing Applications. Advances in Cryptology – ASIACRYPT 2012, pages 208–225, 2012.
## [2] Dušan Božilov, Maria Eichlseder, Miroslav Kneževic, Baptiste Lambin, Gregor Leander, Thorben Moos, Ventzislav Nikov, Shahram Rasoolzadeh, Yosuke Todo, and Friedrich Wiemer
##     PRINCEv2 - More Security for (Almost) No Overhead

## ----------- Instructions ------------ ##
## This is a reference implementation of PRINCE [1] and PRINCEv2 [2].
## Use Test() to check the test vectors (available in [1, 2]).
## Use Encrypt(key, message) or Decrypt(key, message) for encryption/decryption.


## ----------------------------------------------------------------------
## Constants
SBox = [0xB, 0xF, 0x3, 0x2, 0xA, 0xC, 0x9, 0x1, 0x6, 0x7, 0x8, 0x0, 0xE, 0x5, 0xD, 0x4]
InvSBox = [0xB, 0x7, 0x3, 0x2, 0xF, 0xD, 0x8, 0x9, 0xA, 0x6, 0x4, 0x0, 0x5, 0xE, 0xC, 0x1]

ALPHA = [0xC, 0x0, 0xA, 0xC, 0x2, 0x9, 0xB, 0x7, 0xC, 0x9, 0x7, 0xC, 0x5, 0x0, 0xD, 0xD]
BETA = [0x3, 0xF, 0x8, 0x4, 0xD, 0x5, 0xB, 0x5, 0xB, 0x5, 0x4, 0x7, 0x0, 0x9, 0x1, 0x7]

RC = [  ## round constants RC0-5 (RC6-11 can be derived using ALPHA and BETA)
    [0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
    [0x1, 0x3, 0x1, 0x9, 0x8, 0xA, 0x2, 0xE, 0x0, 0x3, 0x7, 0x0, 0x7, 0x3, 0x4, 0x4],
    [0xA, 0x4, 0x0, 0x9, 0x3, 0x8, 0x2, 0x2, 0x2, 0x9, 0x9, 0xF, 0x3, 0x1, 0xD, 0x0],
    [0x0, 0x8, 0x2, 0xE, 0xF, 0xA, 0x9, 0x8, 0xE, 0xC, 0x4, 0xE, 0x6, 0xC, 0x8, 0x9],
    [0x4, 0x5, 0x2, 0x8, 0x2, 0x1, 0xE, 0x6, 0x3, 0x8, 0xD, 0x0, 0x1, 0x3, 0x7, 0x7],
    [0xB, 0xE, 0x5, 0x4, 0x6, 0x6, 0xC, 0xF, 0x3, 0x4, 0xE, 0x9, 0x0, 0xC, 0x6, 0xC],
]


## ----------------------------------------------------------------------
## Auxiliary functions
def AddRoundConst(number, A, v2=False):
    if number > 5:  ## map RC6-11 to RC5-0
        rc = RC[abs(number - 11)]

        if (
            v2 and number % 2 == 1
        ):  ## additionally XOR round constant with BETA (only for PRINCEv2 odd round numbers) or ALPHA
            rc_modifier = BETA
        else:
            rc_modifier = ALPHA
    else:  ## RC0-5 can be used without modification
        rc = RC[number]
        rc_modifier = RC[0]

    for i in range(16):
        A[i] = A[i] ^ rc[i] ^ rc_modifier[i]

    return A


def KeySchedule(number, K, v2=False):
    if not v2:  # PRINCE: round key is always K1
        return K[1]
    else:  # PRINCEv2: round key alternates between K0 and K1
        return K[number % 2]


def AddKey(A, K):
    for i in range(16):
        A[i] = A[i] ^ K[i]
    return A


def SBoxLayer(A):
    for i in range(16):
        A[i] = SBox[A[i]]
    return A


def InvSBoxLayer(A):
    for i in range(16):
        A[i] = InvSBox[A[i]]
    return A


def MPrimeLayer(A):
    T = []
    for i in range(16):
        T.append(0x0)
    for i in range(2):
        T[0 + 12 * i] = (
            ((A[1 + 12 * i] ^ A[2 + 12 * i] ^ A[3 + 12 * i]) & 0x8)
            + ((A[0 + 12 * i] ^ A[2 + 12 * i] ^ A[3 + 12 * i]) & 0x4)
            + ((A[0 + 12 * i] ^ A[1 + 12 * i] ^ A[3 + 12 * i]) & 0x2)
            + ((A[0 + 12 * i] ^ A[1 + 12 * i] ^ A[2 + 12 * i]) & 0x1)
        )

        T[1 + 12 * i] = (
            ((A[0 + 12 * i] ^ A[1 + 12 * i] ^ A[2 + 12 * i]) & 0x8)
            + ((A[1 + 12 * i] ^ A[2 + 12 * i] ^ A[3 + 12 * i]) & 0x4)
            + ((A[0 + 12 * i] ^ A[2 + 12 * i] ^ A[3 + 12 * i]) & 0x2)
            + ((A[0 + 12 * i] ^ A[1 + 12 * i] ^ A[3 + 12 * i]) & 0x1)
        )

        T[2 + 12 * i] = (
            ((A[0 + 12 * i] ^ A[1 + 12 * i] ^ A[3 + 12 * i]) & 0x8)
            + ((A[0 + 12 * i] ^ A[1 + 12 * i] ^ A[2 + 12 * i]) & 0x4)
            + ((A[1 + 12 * i] ^ A[2 + 12 * i] ^ A[3 + 12 * i]) & 0x2)
            + ((A[0 + 12 * i] ^ A[2 + 12 * i] ^ A[3 + 12 * i]) & 0x1)
        )

        T[3 + 12 * i] = (
            ((A[0 + 12 * i] ^ A[2 + 12 * i] ^ A[3 + 12 * i]) & 0x8)
            + ((A[0 + 12 * i] ^ A[1 + 12 * i] ^ A[3 + 12 * i]) & 0x4)
            + ((A[0 + 12 * i] ^ A[1 + 12 * i] ^ A[2 + 12 * i]) & 0x2)
            + ((A[1 + 12 * i] ^ A[2 + 12 * i] ^ A[3 + 12 * i]) & 0x1)
        )

        T[4 + 4 * i] = (
            ((A[4 + 4 * i] ^ A[5 + 4 * i] ^ A[6 + 4 * i]) & 0x8)
            + ((A[5 + 4 * i] ^ A[6 + 4 * i] ^ A[7 + 4 * i]) & 0x4)
            + ((A[4 + 4 * i] ^ A[6 + 4 * i] ^ A[7 + 4 * i]) & 0x2)
            + ((A[4 + 4 * i] ^ A[5 + 4 * i] ^ A[7 + 4 * i]) & 0x1)
        )

        T[5 + 4 * i] = (
            ((A[4 + 4 * i] ^ A[5 + 4 * i] ^ A[7 + 4 * i]) & 0x8)
            + ((A[4 + 4 * i] ^ A[5 + 4 * i] ^ A[6 + 4 * i]) & 0x4)
            + ((A[5 + 4 * i] ^ A[6 + 4 * i] ^ A[7 + 4 * i]) & 0x2)
            + ((A[4 + 4 * i] ^ A[6 + 4 * i] ^ A[7 + 4 * i]) & 0x1)
        )

        T[6 + 4 * i] = (
            ((A[4 + 4 * i] ^ A[6 + 4 * i] ^ A[7 + 4 * i]) & 0x8)
            + ((A[4 + 4 * i] ^ A[5 + 4 * i] ^ A[7 + 4 * i]) & 0x4)
            + ((A[4 + 4 * i] ^ A[5 + 4 * i] ^ A[6 + 4 * i]) & 0x2)
            + ((A[5 + 4 * i] ^ A[6 + 4 * i] ^ A[7 + 4 * i]) & 0x1)
        )

        T[7 + 4 * i] = (
            ((A[5 + 4 * i] ^ A[6 + 4 * i] ^ A[7 + 4 * i]) & 0x8)
            + ((A[4 + 4 * i] ^ A[6 + 4 * i] ^ A[7 + 4 * i]) & 0x4)
            + ((A[4 + 4 * i] ^ A[5 + 4 * i] ^ A[7 + 4 * i]) & 0x2)
            + ((A[4 + 4 * i] ^ A[5 + 4 * i] ^ A[6 + 4 * i]) & 0x1)
        )

    for i in range(16):
        A[i] = T[i]
    return A


def ShiftRows(A):
    temp = A[1]
    for i in range(3):
        A[1 + 4 * i] = A[5 + 4 * i]
    A[13] = temp

    temp = A[2]
    A[2] = A[10]
    A[10] = temp
    temp = A[6]
    A[6] = A[14]
    A[14] = temp

    temp = A[15]
    for i in range(3):
        A[15 - 4 * i] = A[11 - 4 * i]
    A[3] = temp
    return A


def InvShiftRows(A):
    temp = A[13]
    for i in range(3):
        A[13 - 4 * i] = A[9 - 4 * i]
    A[1] = temp

    temp = A[2]
    A[2] = A[10]
    A[10] = temp
    temp = A[6]
    A[6] = A[14]
    A[14] = temp

    temp = A[3]
    for i in range(3):
        A[3 + 4 * i] = A[7 + 4 * i]
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


def Round(number, A, K, v2=False):
    A = SBoxLayer(A)
    A = MLayer(A)
    A = AddRoundConst(number, A, v2=v2)
    round_key = KeySchedule(number, K, v2=v2)
    A = AddKey(A, round_key)
    return A


def InvRound(number, A, K, v2=False):
    round_key = KeySchedule(number, K, v2=v2)
    A = AddKey(A, round_key)
    A = AddRoundConst(number, A, v2=v2)
    A = InvMLayer(A)
    A = InvSBoxLayer(A)
    return A


def PrinceReflector(A, K, v2=False, decryption=False):
    A = SBoxLayer(A)

    if v2:  ## PRINCEv2: extra K0 addition
        A = AddKey(A, K[0])

    A = MPrimeLayer(A)

    if v2 and decryption:  ## PRINCEv2: modification to second half of round keys
        for i in range(16):
            K[0][i] = K[0][i] ^ ALPHA[i] ^ BETA[i]
            K[1][i] = K[1][i] ^ ALPHA[i] ^ BETA[i]

    if v2:  ## PRINCEv2: extra K1 XOR RC11 addition
        A = AddKey(A, K[1])
        A = AddRoundConst(11, A, v2=v2)

    A = InvSBoxLayer(A)
    return A, K


def CreateNibbles(message, key):
    A = []
    K0 = []
    K1 = []

    for i in range(16):
        a = (message >> (60 - i * 4)) & 0xF
        k0 = (key[0] >> (60 - i * 4)) & 0xF
        k1 = (key[1] >> (60 - i * 4)) & 0xF
        A.append(a)
        K0.append(k0)
        K1.append(k1)
    return A, [K0, K1]


def IntegerFromNibbles(A):
    ciphertext = 0x0
    for i in range(16):
        ciphertext = ciphertext ^ A[i]
        if i != 15:
            ciphertext = ciphertext << 4
    return ciphertext


## ----------------------------------------------------------------------
## Message as a 64-bit integer, key as [key_0,key_1] - both 64-bit integers.
def PrinceCore(key, message, v2=False, decryption=False):
    ## internal state and the key matrix
    A, K = CreateNibbles(message, key)

    ## key addition
    round_key = KeySchedule(0, K, v2=v2)
    A = AddKey(A, round_key)

    ## the first round constant
    A = AddRoundConst(0, A, v2=v2)

    ## forward rounds
    for i in range(1, 6):
        A = Round(i, A, K, v2=v2)

    ## reflector
    A, K = PrinceReflector(A, K, v2=v2, decryption=decryption)

    ## backward rounds
    for i in range(6, 11):
        A = InvRound(i, A, K, v2=v2)

    ## the last round constant
    A = AddRoundConst(11, A, v2=v2)

    ## key addition
    round_key = KeySchedule(11, K, v2=v2)
    A = AddKey(A, round_key)

    ## integer from nibbles
    ciphertext = IntegerFromNibbles(A)

    return ciphertext


## ----------------------------------------------------------------------
## k_0 as a 64-bit integer.
def WhiteningKeyTransform(k_0):
    ## ror k_0, 1
    temp_a = (k_0 >> 1) | ((k_0 & 0b1) << 63)
    temp_b = k_0 >> 63

    k_0_prime = temp_a ^ temp_b

    return k_0_prime


## ----------------------------------------------------------------------
## Plaintext as a 64-bit integer, key as [key_0,key_1] - both 64-bit integers.
def Encrypt(key, plaintext, v2=False):
    if not v2:  ## PRINCE: pre-whitening key addition
        plaintext = key[0] ^ plaintext

    ciphertext = PrinceCore(key, plaintext, v2=v2)

    if not v2:  ## PRINCE: post-whitening key addition
        k0_prime = WhiteningKeyTransform(key[0])
        ciphertext = k0_prime ^ ciphertext

    return ciphertext


## ----------------------------------------------------------------------
## Ciphertext as a 64-bit integer, key as [key_0,key_1] - both 64-bit integers.
def Decrypt(key, ciphertext, v2=False):
    if not v2:  ## PRINCE: pre-whitening key addition and K1 becomes K1 XOR ALPHA
        k0_prime = WhiteningKeyTransform(key[0])
        ciphertext = k0_prime ^ ciphertext
        key[1] = key[1] ^ IntegerFromNibbles(ALPHA)
    else:  ## PRINCEv2: K0 becomes K1 XOR BETA and K1 becomes K0 XOR ALPHA
        k0 = key[1] ^ IntegerFromNibbles(BETA)
        k1 = key[0] ^ IntegerFromNibbles(ALPHA)
        key = [k0, k1]

    plaintext = PrinceCore(key, ciphertext, v2=v2, decryption=True)

    if not v2:  ## PRINCE post-whitening key addition
        plaintext = key[0] ^ plaintext

    return plaintext


## ----------------------------------------------------------------------
## Test vectors and correctness check.
def Test():
    test_vectors = [  ## format: [plaintext, k0, k1, PRINCE ciphertext, PRINCEv2 ciphertext]
        [0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x818665AA0D02DFDA, 0x0125FC7359441690],
        [0xFFFFFFFFFFFFFFFF, 0x0000000000000000, 0x0000000000000000, 0x604AE6CA03C20ADA, 0x832BD46F108E7857],
        [0x0000000000000000, 0xFFFFFFFFFFFFFFFF, 0x0000000000000000, 0x9FB51935FC3DF524, 0xEE873B2EC447944D],
        [0x0000000000000000, 0x0000000000000000, 0xFFFFFFFFFFFFFFFF, 0x78A54CBE737BB7EF, 0x0AC6F9CD6E6F275D],
        # fifth test vector available in [1, 2] is not included because k0 differs
    ]

    for i, tv in enumerate(test_vectors):
        pt, k0, k1, expected_ct_prince, expected_ct_princev2 = tv

        for v2 in [False, True]:
            cipher = "PRINCEv2" if v2 else "PRINCE"
            expected_ct = expected_ct_princev2 if v2 else expected_ct_prince
            ct = Encrypt([k0, k1], pt, v2=v2)
            received_pt = Decrypt([k0, k1], ct, v2=v2)

            assert (
                expected_ct == ct
            ), f"{cipher} encryption failed on test vector #{i+1}: expected {hex(expected_ct)}, but received {hex(ct)}"
            assert (
                received_pt == pt
            ), f"{cipher} decryption failed on test vector #{i+1}: expected {hex(pt)}, but received {hex(received_pt)}"

    print("PRINCE and PRINCEv2 passed all 4 test vectors!")


if __name__ == "__main__":
    Test()
