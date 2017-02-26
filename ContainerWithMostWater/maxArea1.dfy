method maxArea(a: array<int>) returns (max: int)
	requires a != null && 2 <= a.Length;
	ensures forall i,j :: 0<= i < j < a.Length ==> max >= a[i]*(j-i) || max >= a[j]*(j-i);
{
	max := 100;
	var l:= 0;
	while(l < a.Length - 1)
		invariant 0 <= l < a.Length;
		invariant forall i,j :: 0<= i < l && i < j < a.Length ==> max >= a[i]*(j-i) || max >= a[j]*(j-i);
		decreases a.Length - 1 - l;
	{
		var r := l + 1;
		while(r < a.Length)
			invariant 0 <= l < r <= a.Length;
			invariant forall i,j :: 0<= i < l && i < j < a.Length ==> max >= a[i]*(j-i) || max >= a[j]*(j-i);
			invariant forall j :: l < j < r ==> max >= a[l]*(j-l) || max >= a[j]*(j-l);
			decreases a.Length - r;
		{
			if(a[l] <= a[r])
			{
				if(a[l]*(r - l) > max)
				{
					max := a[l]*(r - l);
				}
			}
			else
			{
				if(a[r]*(r - l) > max)
				{
					max := a[l]*(r - l);
				}
			}
			r := r + 1;
		}
		l := l + 1;
	}
	return max;
}  