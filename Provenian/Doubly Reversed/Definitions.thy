theory Definitions
imports Main
begin

datatype 'a list = nil | cons 'a "'a list"

primrec append where
  "append nil ys = ys"
| "append (cons x xs) ys = cons x (append xs ys)"

primrec reverse where
  "reverse nil = nil"
| "reverse (cons x xs) = append (reverse xs) (cons x nil)"

end
