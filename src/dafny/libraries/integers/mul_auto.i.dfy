include "mul_auto_proofs.i.dfy"

module Math__mul_auto_i {
import opened Math__mul_auto_proofs_i

predicate MulAuto()
{
    (forall x:int, y:int :: x * y == y * x)
 && (forall x:int, y:int, z:int  :: (x + y) * z == x * z + y * z)
 && (forall x:int, y:int, z:int  :: (x - y) * z == x * z - y * z)
}

lemma lemma_mul_auto()
    ensures  MulAuto();
{
    lemma_mul_auto_commutes();
    lemma_mul_auto_distributes();
}

predicate TMulAutoLe(x:int, y:int) { x <= y }

lemma lemma_mul_auto_induction(x:int, f:imap<int,bool>)
    requires forall i :: i in f;
    requires MulAuto() ==> f[0]
                        && (forall i :: TMulAutoLe(0, i) && f[i] ==> f[i + 1])
                        && (forall i :: TMulAutoLe(i, 0) && f[i] ==> f[i - 1]);
    ensures  MulAuto();
    ensures  f[x];
{
    lemma_mul_auto_commutes();
    lemma_mul_auto_distributes();
    assert forall i :: TMulAutoLe(0, i) && f[i] ==> f[i + 1];
    assert forall i :: TMulAutoLe(i, 0) && f[i] ==> f[i - 1];
    lemma_mul_induction_forall(f);
    assert f[x];
}

lemma lemma_mul_auto_induction_forall(f:imap<int,bool>)
    requires forall i :: i in f;
    requires MulAuto() ==> f[0]
                        && (forall i :: TMulAutoLe(0, i) && f[i] ==> f[i + 1])
                        && (forall i :: TMulAutoLe(i, 0) && f[i] ==> f[i - 1]);
    ensures  MulAuto();
    ensures  forall i  :: f[i];
{
    lemma_mul_auto_commutes();
    lemma_mul_auto_distributes();
    assert forall i :: TMulAutoLe(0, i) && f[i] ==> f[i + 1];
    assert forall i :: TMulAutoLe(i, 0) && f[i] ==> f[i - 1];
    lemma_mul_induction_forall(f);
}

} 
