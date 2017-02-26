method max(a: array<int>) returns (res: int)
  requires a!= null;
  ensures forall i: int :: 0 <= i < a.Length ==> a[i] <= res
  ensures (a.Length > 0)==> (exists i: int :: 0 <= i < a.Length && a[i] == res)
  {
    if(a.Length == 0){
      res := 0;
    }
    else{
      res := a[0];
      var i := 1;
      while (i < a.Length)
      invariant i <= a.Length
      invariant (forall j: int :: 0 <= j < i ==>  a[j] <= res)
      invariant (exists j: int :: 0 <= j < i && a[j] == res)
      decreases (a.Length-i); 
      {
        if(a[i] > res){
          res := a[i];
        }
        i := i + 1;
      }
    }
  }