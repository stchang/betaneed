# betaneed

Redex models for "The Call-by-need Lambda Calculus, Revisited", Chang and Felleisen, ESOP 2012.

### Description of files:

#### Main file (start here)
- cbneednew

#### Equivalent semantics
- cbneednew-CK: CK machine
- cbneednew-deref: cbneednew with deref instead of subst; a stepping stone from AF to cbneednew(?)
- cbneednew-deref-CK: CK machine of cbneednew-deref
- launchbury-CKH: Launchbury semantics with heap
- lazystep: a parallel reduction semantics, used by racket lazy stepper (see also Chang et al. IFL 2011)

#### Proofs
- cbneednew-cr: Church-Rosser proof
- cbneednew-sr: standard reduction proof
- cbneednew-examples: examples showing redexes with various context shapes
- CR: Church-Rosser for AF cbneed
- SR: standard reduction for AF cbneed

#### Tests
- cbneednew-lang-tests
- cbneednew-red-tests
- cbneednew-redexcheck-CK: check cbneednew equiv to CK
- cbneednew-redexcheck-CK-CKH: check that CK equivalent to CKH
- cbneednew-redexcheck-CK-lazystep
- cbneednew-redexcheck-deref-CK
- cbneednew-redexcheck-deref
- cbneednew-redexcheck: check cbneednew equiv to AF cbneed
- launchbury-redexcheck-CKH: check cbneednew equiv to Launchbury
- lazystep-redexcheck