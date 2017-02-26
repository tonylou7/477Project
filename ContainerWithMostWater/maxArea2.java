
public class maxArea2 {
	public int maxArea(int[] a) {
        int maxarea = 0;
        int l = 0;
        int r = a.length - 1;
        while (l < r) {
            maxarea = Math.max(maxarea, Math.min(a[l], a[r]) * (r - l));
            if (a[l] < a[r]) l++;
            else r--;
        }
        return maxarea;
    }
}
