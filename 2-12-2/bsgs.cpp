#include <iostream>
#include <cmath>
#include <unordered_map>
#include <cstdint>
using namespace std;
uint32_t pow_m(uint32_t base, uint32_t pow, uint32_t mod)
{
	if(pow == 0)
		return 1;
	else if(pow%2 == 0){
		uint32_t res = pow_m(base, pow/2, mod);
		return res*res % mod;
	}
	else{
		uint32_t res = pow_m(base, pow/2, mod);
		return res*res*base % mod;
	}
	return -1;
}

uint32_t bsgs(uint32_t N, uint32_t g, uint32_t h)
{
	uint32_t m = ceil(sqrt(N));
	auto table = unordered_map<uint32_t, uint32_t>{};
	uint64_t e = 1;
	for(uint32_t i = 0; i < m; i++){
		table[static_cast<uint32_t>(e)] = i;
		e = e * g % N;
	}
	const uint32_t factor = pow_m(g, N-m-1, N);
	e = h;
	for(uint32_t i = 0; i < m; i++){
		if( auto it = table.find(static_cast<uint32_t>(e)); it != table.end()){
			return i*m + it->second;
		}
		e = e * factor % N;
	}
	return -1;
}

int main()
{
	auto ans = bsgs(13, 2, 3);
	if(ans != -1)
		cout << ans << endl;
	else 
		cout << "fuck!\a\n";
	return 0;
}
