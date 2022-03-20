# WIP Prolog Compiler Experiments

## Example
1. Load `mini-haskell.pl`
2. Start the repl:
    ```prolog
    -? repl.
    ```
3. Enter a term such as:
    ```prolog
    |: f->x->y->(f@(x+y) == f@(mappend@x@y)).
    f->x->y->f@(x+y)==f@(mappend@x@y) : (A->B)->A->A->bool
        where
        A implements Add + Monoid
        B implements Eq
    ```
4. Exit the repl with `quit`
    ```prolog
    |: quit.
    ```