# How to install

This sections documents how to install LH and its dependencies.

## External software requirements

In order to use `liquidhaskell`, you will need a [SMT solver](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories)
installed on your system. Download and install at least one of:

* [Z3](https://github.com/Z3Prover/z3) or [Microsoft official binary](https://www.microsoft.com/en-us/download/details.aspx?id=52270)
* [CVC4](https://cvc4.github.io/)
* [MathSat](https://mathsat.fbk.eu/)

Note: The SMT solver binary should be on your `PATH`; LiquidHaskell will execute it as a child process.

## Next

Once installed, you can now install and use LH as [a plugin](plugin.md) or legacy [executable](legacy.md).
