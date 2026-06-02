# PRINCE and PRINCEv2
A Python 3 reference implementation of the lightweight block ciphers [PRINCE](https://eprint.iacr.org/2012/529) and [PRINCEv2](https://eprint.iacr.org/2020/1269). This is a fork of [the PRINCE repository by David Tvrdý](https://github.com/DavidTvrdy/PRINCE) with the following modifications:

- Additional implementation of PRINCEv2, integrated into the original repository's PRINCE implementation
- The PRINCE(v2) state `A` is used as a function argument instead of a global variable, making it possible to use helper functions individually.
- 

The implementation works on the test vectors provided by the authors of the ciphers. It is a straightforward, unoptimized implementation.
No effort has been made to defend against side-channel or any other kind of attacks.
