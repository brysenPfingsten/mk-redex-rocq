; The recursive branch comes first. The base clause uses a fresh variable.
(program
  (relations
    (relation 1
      (disj (call 0 (par 0))
        (fresh 1
          (conj (unify (par 0) (nat 7))
                (unify (par 1) (par 0)))))))
  (counter 1)
  (query 0)
  (goal (call 0 (var 0))))
