
to check:

- epoch processing defs of EBBs, justified



//

1. prove that an EBB is justified (in code) iff is justified by definition
    
2. for finalisation, try to do the same as 1. using only one way of finalising EBB 
    (for safety this is enough), although we probably only prove the if direction only. 


Proofs:
a. s.current_justified_checkpoint must be the highest epoch justified checkpoint 
b. valid attestations must have s.current_justified_checkpoint as source 
    because we copy them into previous_attestations same applies to previous_attestations 
c. consequence: a supermajority link in s.current_attestations must be from 
    s.current_justified_checkpoint 
d. because this one is justified, then updateJustification is correct.

need to change definition of justified.
1. use only attestations for target epoch i 
2. assume epochs prior i are defined as justified or not 

start with 1-finalisation to prove property lemma 5.11
