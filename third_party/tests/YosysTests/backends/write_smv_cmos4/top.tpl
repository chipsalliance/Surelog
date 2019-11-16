; we need QF_UFBV for this poof
        (set-logic QF_UFBV)

        ; insert the auto-generated code here
        %%

        ; declare two state variables s1 and s2
        (declare-fun s1 () test_s)
        (declare-fun s2 () test_s)

        ; state s2 is the successor of state s1
        (assert (test_t s1 s2))

        ; we are looking for a model with y non-zero in s1
        (assert (distinct (|test_n y| s1) #b0000))

        ; we are looking for a model with y zero in s2
        (assert (= (|test_n y| s2) #b0000))

        ; is there such a model?
        (check-sat)
 
