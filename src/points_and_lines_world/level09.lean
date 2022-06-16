import data.set.basic -- hide
import data.set.prod --hide
open set -- hide

variables {X Y : Type} -- hide

/- Tactic : split

## Summary:

If the goal is `P ∧ Q` or `P ↔ Q` then `split` will break it into two goals.

## Details

If `P Q : Prop` and the goal is `⊢ P ∧ Q`, then `split` will change it into
two goals, namely `⊢ P` and `⊢ Q`. 

If `P Q : Prop` and the goal is `⊢ P ↔ Q`, then `split` will change it into
two goals, namely `⊢ P → Q` and `⊢ Q → P`.  

## Example:

If your local context (the top right window) looks like this
```
X : Type
A B : set X
x : X
⊢ x ∈ A ↔ x ∈ B
```

then after

`split,`

it will look like this:

```
2 goals
X : Type
A B : set X
x : X
⊢ x ∈ A → x ∈ B


X : Type
A B : set X
x : X
⊢ x ∈ B → x ∈ A
```
-/

/-
In this level we will learn the `split` tactic. It breaks a goal `P ∧ Q` into two goals (proving `P`, and then proving `Q`),
and also breaks goals of the form `P ↔ Q` into proving each of the implications separately.

You will need to use both features to accomplish this proof.
-/

