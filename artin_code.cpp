#include <iostream>
#include <vector>
#include <bitset>
#include <iomanip>
#include <algorithm>
#include <math.h>
#include <unordered_map>

using namespace std;

typedef long long ll;
// typedef pair pii;
// typedef vector vi;
typedef long double ld;

const ll N = 1e8 + 5;

bool pr[N]; //Prime/composite info for n < N.
ll gpd[N];

void sieve() {
	for(int i = 2; i < N; ++i) {
		pr[i] = true;
	}
	for(ll p = 2; p < N; ++p) {
		if(!pr[p]) continue;
        gpd[p] = p;
		for(ll j = 2*p; j < N; j+=p) {
			pr[j] = false;
            gpd[j] = p;
		}
    }

}

ll exp(ll a, ll e) {
    ll ans = 1;
    ll A = a;
    while(e > 0) {
        if(e%2 == 1) ans *= A;
        A *= A;
        e /= 2;
    }
    return ans;
}

inline ll gcd(ll a, ll b) {
    if(a > b) return gcd(b, a);
    while(a > 0) {
        ll c = b%a;
        b = a;
        a = c;
    }
    return b;
}

inline ll lcm(ll a, ll b) { return (a*b)/gcd(a, b);}

ll phi(ll n) {
    ll ans = 1;
    if(n < N) {
        while(n > 1) {
            ll p = gpd[n];
            ll q = p-1;
            n /= p;
            while(n%p == 0) {
                q *= p;
                n /= p;
            }
            ans *= q;
        }
        return ans;
    } else {
        for(int p = 2; p*p <= n; ++p) {
            if(n%p == 0) {
                ll q = p-1;
                n /= p;
                while(n%p == 0) {
                    q *= p;
                    n /= p;
                }
                ans *= q;
                if(n < N) return ans*phi(n);
            }
        }
    }
    abort();
}

const ld EPS = 1e-9;

inline ll mu(ll n) {
    if(n <= 6) {
        if(n == 1 || n == 6) return 1;
        if(n == 2 || n == 3) return -1;
    }
    ll ans = 1;
    while(n > 1) {
        ll p = gpd[n];
        n /= p;
        if(n%p == 0) return 0;
        ans *= -1;
    }
    return ans;
}


inline ll get_vq(ll a, ll q) {
    ll v = 0;
    while(a%q == 0) {
        v += 1;
        a /= q;
    }
    return v;
}

inline ll get_pd(ll a) {
    if(a < N) return gpd[a];
    for(ll q = 2; q*q <= a; ++q) {
        if(a%q == 0) return q;
    }
    abort();
}

inline ld get_galois_correction(ll a, ll b) {
    ld D = 1;
    bool div8 = (a%8 == 0 || b%8 == 0);
    bool div4 = (a%4 == 0 || b%4 == 0);
    bool div3 = (a%3 == 0 || b%3 == 0);
    if(div8 && a%2 == 0) D /= 2;
    if(div3 && div4 && b%2 == 0) D /= 2;
    return D;
}


ld get_f(ll a, ll b) {
    ld sum = 0;
    for(int n1 = 1; n1 <= 6; ++n1) {
        for(int n2 = 1; n2 <= 6; ++n2) {
            if(6%n1 != 0 || 6%n2 != 0) continue;
            ld deg = phi(lcm(a*n1, b*n2))*a*n1*b*n2;
            deg *= get_galois_correction(a*n1, b*n2);
            sum += (ld) mu(n1)*mu(n2)/deg;
        }
    }
    sum *= phi(lcm(a, b))*a*b;
    return sum;
}

ld getExp(ll q, ll k) {
    ld Q = 1;
    while(k > 0) {
        Q *= q;
        k -= 1;
    }
    return Q;
}

ld getPhi(ll q, ll k) {
    if(k == 0) return 1;
    ld Q = (ld) (q-1)*getExp(q, k-1);
    return Q;
}

ld get_gqkk(ll q, ll k) {
    if(k == 0) {
        ld Q = (ld) q;
        return 1 - 2/(Q*(Q-1)) + 1/(Q*Q*(Q-1));
    }
    ld ans = 0;
    for(ll n1 = 0; n1 <= 1; ++n1) {
        for(ll n2 = 0; n2 <= 1; ++n2) {
            ld sign = 1; if(n1 == 1) sign *= -1; if(n2 == 1) sign *= -1;
            ans += sign/(getPhi(q, max(k+n1, k+n2))*getExp(q, 2*k+n1+n2));
        }
    }
    return ans;
}

ld get_gqk1k2(ll q, ll k1, ll k2) {
    ld ans = 0;
    for(ll n1 = 0; n1 <= 1; ++n1) {
        for(ll n2 = 0; n2 <= 1; ++n2) {
            ld sign = 1; if(n1 == 1) sign *= -1; if(n2 == 1) sign *= -1;
            ans += sign/(getPhi(q, max(k1+n1, k2+n2))*getExp(q, k1+n1+k2+n2));
        }
    }
    return ans;
}


inline ld get_six(ll a) {
    ll A = 1;
    while(a%2 == 0) {
        A *= 2;
        a /= 2;
    }
    while(a%3 == 0) {
        A *= 3;
        a /= 3;
    }
    return A;
}

unordered_map<ll, ld> f_vals; //A bit of caching, probably doesn't matter.
ll HC = 1e9;

ld get_dens(ll a, ll b) {
    ll a6 = get_six(a);
    ll b6 = get_six(b);
    
    ld ans = f_vals[HC*a6 + b6];
    a /= a6;
    b /= b6;
    if(a < b) swap(a, b);
    while(a > 1) {
        ll q = get_pd(a);
        ll va = 0;
        ll vb = 0;
        while(a%q == 0) {
            a /= q;
            ++va;
        }
        while(b%q == 0) {
            b /= q;
            ++vb;
        }

        ans *= get_gqk1k2(q, va, vb)/get_gqkk(q, 0);
        
        if(a < b) swap(a, b);
    } 
    return ans;
}

ld get_gpk(ll q, ll k) {
    ld Q = (ld) q;
    if(k == 0) {
        return 1 - 1/(Q*(Q-1));
    }
    ld term = 1 - 1/(Q*Q); term *= 1/(getPhi(Q, k)*getExp(Q, k));
    return term;
}

ld get_one_dens(ll a) {
    ll a2 = 1;
    while(a%2 == 0) {
        a /= 2;
        a2 *= 2;
    }
    ld ans = 1;
    if(a2 == 1) ans = 0.5;
    else if(a2 == 2) ans = 0.375;
    else if(a2 == 4) ans = 0.0625;
    else ans = (ld) 3/(a2*a2);
    while(a > 1) {
        ll q = get_pd(a);
        ll va = 0;
        while(a%q == 0) {
            a /= q;
            ++va;
        }
        ans *= get_gpk(q, va)/get_gpk(q, 0);
    }
    return ans;
}

inline bool smooth(ll a, ll x) {
    if(a < N) return (gpd[a] <= x);
    for(ll p = 2; p <= x; ++p) {
        while(a%p == 0) a /= p;
    }
    return (a==1);
}

int main() {
	//Perform sieve computation
	sieve();
	cout << setprecision(11);
	cout << fixed;

    ll x = 1e8;
    ll T = 1e6;

    ld prod = 1;
    ld prodA = 1;
    for(int q = 5; q <= x; ++q) {
        if(!pr[q]) continue;
        prod *= get_gqkk(q, 0);
        prodA *= get_gpk(q, 0);
    }
    prodA *= get_gpk(3, 0);

    ld sum = 0;
    for(ll a = 1; a <= T; ++a) {
        if(!smooth(a, 3)) continue;
        for(ll b = 1; b <= T; ++b) {
            if(!smooth(b, 3)) continue;
            f_vals[HC*a + b] = (ld) get_f(a, b)/(phi(lcm(a, b))*a*b);
        }
    }
    
    for(ll a = 1; a <= T; ++a) {
        sum += get_one_dens(a)*prodA;
        for(int b = 1; b <= a; ++b) {
            sum -= get_dens(a, b)*prod; //This inner loop is what takes >99% of the time.
        }
    }

    cout << sum << "\n";
}
