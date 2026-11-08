; appendo([1,2], [3], q0): expected q0 = [1,2,3].
(program
  (relations standard)
  (counter 1)
  (query 0)
  (goal (call 0 (cons (nat 1) (cons (nat 2) nil))
                (cons (nat 3) nil) (var 0))))
