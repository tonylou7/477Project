method moveZero(a: array<int>) returns (first0: int)
  requires a != null && a.Length > 0;
  modifies a;
  ensures a.Length == old(a.Length);
  ensures forall j :: 0 <= j < first0 <= a.Length ==> a[j] != 0;
  ensures forall j :: 0 <= first0 <= j < a.Length ==> a[j] == 0;
  ensures multiset(a[..]) == old(multiset(a[..]));
{
  first0 := 0;
  var cur := 0;
  while(cur < a.Length)
  invariant 0 <= first0 <= cur <= a.Length;
  invariant forall j :: 0 <= j < first0 <= a.Length ==> a[j] != 0;
  invariant forall j :: 0 <= first0 <= j < cur <= a.Length ==> a[j] == 0;
  invariant multiset(a[..]) == old(multiset(a[..]));
  {
    if(a[cur] != 0){
      swap(a, first0, cur);
      first0 := first0 + 1;
    }
    cur := cur + 1;
  }
  return first0;
}
method swap(a: array<int>, i: int, j: int)
  requires a != null && 0 <= i <= j < a.Length;
  modifies a;
  ensures a[i] == old(a[j]);
  ensures a[j] == old(a[i]);
  ensures multiset(a[..]) == old(multiset(a[..]));
  ensures forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k]);
{
  var temp := a[i];
  a[i] := a[j];
  a[j] := temp;
}