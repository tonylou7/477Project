method stock(a: array<int>) returns (max: int)
	requires a != null;// && a.Length > 0;
	requires forall i :: 0 <= i < a.Length ==> a[i] <= 1000;
	ensures forall k, j :: 0 <= k < j < a.Length ==> max >= a[j] - a[k];
{
	max := 0;
	if(a.Length < 2){
		return max;
	}
	var lowPrice := a[0];
	var i := 0;
	while( i < a.Length)
		invariant i <= a.Length;
		invariant max >= 0;
		invariant forall j :: 0 <= j < i ==> lowPrice <= a[j];
		invariant forall k,j :: 0 <= k < j < i ==> max >= a[j] - a[k];
		decreases a.Length - i;
	{
		if(a[i] < lowPrice){
			lowPrice := a[i];
		}
		else if(a[i] - lowPrice > max){
			max := a[i] - lowPrice;
		}
		i := i + 1;
	}
	return max;
}