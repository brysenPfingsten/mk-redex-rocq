; appendo(q0, [3], [1,2,3]): expected q0 = [1,2].
(program
  (relations standard)
  (counter 1)
  (query 0)
  (goal (call 0 (var 0) (cons (nat 3) nil)
                (cons (nat 1) (cons (nat 2) (cons (nat 3) nil))))))
