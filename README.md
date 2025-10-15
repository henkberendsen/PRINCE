# PRINCE
A Python 3 reference implementation of the lightweight block cipher PRINCE. This fork modifies the code to use the state `A` as a function argument instead of a global variable, making it possible to use helper functions individually.

The implementation works on the test vectors provided by the authors of the cipher. It is a straightforward, unoptimized implementation.
No effort has been made to defend against side-channel or any other kind of attacks.
