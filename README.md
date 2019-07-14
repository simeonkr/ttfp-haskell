See [TTFP_ex.hs](TTFP_ex.hs) for examples. For instance, the type 
`((∀x:A).(B ⇒ C) ⇒ ((∀x:A).B ⇒ (∀x:A).C))` is inhabited by the lambda expression
`λr.λp.λx.((r x) (p x))` as proven by

```
Prelude> :l TTFP_ex.hs
Prelude> ex5
Right 
λr.λp.λx.((r x) (p x)) : ((∀x:A).(B ⇒ C) ⇒ ((∀x:A).B ⇒ (∀x:A).C))
  λp.λx.((r x) (p x)) : ((∀x:A).B ⇒ (∀x:A).C)
    λx.((r x) (p x)) : (∀x:A).C
      ((r x) (p x)) : C
        (r x) : (B ⇒ C)
          [x : A] *
          [r : (∀x:A).(B ⇒ C)] *
        (p x) : B
          [x : A] *
          [p : (∀x:A).B] *
```

### TODO

* Equality type elimination is untested and currently very difficult to properly use
* Better extensibility (adding new types as Haskell data constructors is cumbersome and messy)
* Advanced types like trees and lists; more examples
* Show rules in pretty-printed proofs