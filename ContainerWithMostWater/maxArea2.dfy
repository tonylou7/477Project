method maxArea(a: array<int>) returns (max: int)
	requires a != null && a.Length > 1;
	//ensures forall i, j :: 0<= i < j < a.Length && a[i] <= a[j] ==> max >= a[i]*(j-i);
	//ensures forall i, j :: 0<= i < j < a.Length && a[i] > a[j] ==> max >= a[j]*(j-i);
	//ensures forall i, j :: 0<= i <j < a.Length ==> (max >= a[i]*(j-i) || max >= a[j]*(j-i));//||
	//(0<= i < k <=j < a.Length ==> (max >= a[i]*(j-i) || max >= a[j]*(j-i)));
	//(forall i, j :: 

{
	max := 0;
	if(a.Length < 2)
	{
		return max;
	}
	var L := 0;
	var R := a.Length - 1;
	var height := 0;
	while(L < R)
		invariant max >= 0;
		invariant a == old(a);
		invariant 0<= L <= R < a.Length;
		invariant forall i, j :: 0<= i < L <= R< j < a.Length && a[i] >= a[j] ==> max >= a[j]*(j-i);
		
		//	((a[i] >= a[j] ==> max >= a[j]*(j-i)) && (a[i] < a[j] ==> max >= a[i]*(j-i)))
	//(max >= a[i]*(j-i) || max >= a[j]*(j-i)); //||
	//(0<= i < l && r<= j < a.Length ==> (max >= a[i]*(j-i) || max >= a[j]*(j-i)));
		decreases R - L;
	{
		if(a[L] <= a[R]){
			height := a[L];
		}else{
			height := a[R];
		}
		if(height * (R-L) > max){
			max := height * (R-L);
		}
		if(a[L] < a[R]){
			L := L+ 1;
		}else{
			R := R - 1;
		}
	}
	return max;
}