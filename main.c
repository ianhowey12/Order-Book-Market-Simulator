/*

PROCESS

On each frame, we have the time of the next order creation (either limit or market).
We also store the user's last typed action with the time at which they typed it.
We then execute every order creation up to the current time and render the result.
We execute the user's last typed actions along with the participant orders.

The process:
	We generate whether the order is a market or limit order.
	If limit,
		We choose a price and update all limit orders at that price.
		We generate a limit order at that price.
	If market,
		We randomly choose to buy or sell, 50/50.
		We update and fill limit orders starting from the bid going down or from the ask going up until the market order is consumed.
	Next, we move the time of the next order creation to a randomly-generated future time.
	We keep repeating this until the next order creation (whichever one comes first) comes after the time limit.

When running, we need to store:
- A free list for limit orders
- An array list of singly-linked lists of limit orders by increasing price order (first buys and then sells) and then fill priority in each list (head is added last and filled last)
- The bid and ask
- The time of the next order creation

ASSUMPTIONS

We assume:
- That the participants' actions are independent of their previous actions and other participants' actions and of the state of the market
- That their actions are distributed as simulated, with the same rates of effect
- That the participants fill randomly after our market orders fill some limit orders


THINGS WE NEED TO DO TO MAKE THIS ACCURATE/CORRECT

Make sure that the number of limit orders does not approach zero or infinity after a long time.
This involves making the rate of creation slightly greater than the rate of filling and having deletions take a long time.

*/

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <math.h>
#include <time.h>
#include <corecrt_math.h>
#include <conio.h>

typedef unsigned long long u64;
typedef unsigned int u32;

// A limit order waiting to be filled.
typedef struct {
	u32 size;
	u32 p;
	u64 expirationTime; // The time at which this order gets deleted.
	struct limitOrder* next; // Next order at the exact same price (singly-linked list).
	bool user; // Whether this limit order was created by the user.
} limitOrder;

// Free memory to create orders and commands from. These point to locations in the original blocks which are not stored.
limitOrder** freeLimitOrders;
int numFreeLimitOrders = 0;
int poolSize = 1000000;

// Current state of the order book.
#define NUM_PRICES 100000 // Min price is $0.00, max price is $999.99.
limitOrder* limitOrderHead[NUM_PRICES]; // Singly-linked list: the first limit order at this price. Buy/sell depends solely on price's relation to bid and ask.
u32 bid = 0; // Will be the current highest limit buy price after updating.
u32 ask = UINT_MAX; // Will be the current lowest limit sell price after updating.

#define MAX_NUM_USER_LIMIT_ORDERS 100
int numUserLimitOrders = 0;
limitOrder** userLimitOrders = NULL;

int balance = 0;
int sharesOpen = 0;

bool userEditing = 0;
u32 userEditingNumber = 0;
int userSelected = 0;

// Parameters for participant behavior.
double averageOrderCreationDeltaNS = 0.2 * 1e9; // How long between a participant's order and another participant's order.
double averageMarketOrderSize = 8.0;
double averageLimitOrderSize = 10.0;
double averageLimitOrderLifespanNS = 100.0 * 1e9; // How long before a limit order gets deleted.
double averageLimitOrderDistance = 3.0; // Average number of cents a limit buy is below the ask or a limit sell is above the bid.
double marketOrderProbability = 0.5; // Probability of a participant choosing a market order instead of a limit order.
int numOrderBookLines = 19; // The height of the order book as displayed in the console.

// Other settings.
u64 frameLengthNS = 100000000;
u32 initialBidMin = 500;
u32 initialBidMax = 500;
u32 initialSpreadMin = 1;
u32 initialSpreadMax = 1;
u32 userLimitBuySize = 100;
u32 userLimitSellSize = 100;
u32 userMarketBuySize = 100;
u32 userMarketSellSize = 100;
bool realisticUserMarketOrders = 1;
bool fillTiesInStackOrder = 0;


u64 getTime() {
	struct timespec now;
	timespec_get(&now, TIME_UTC);
	return (u64)now.tv_sec * (u64)1000000000 + (u64)now.tv_nsec;
}

u64 randState = 0;
u64 randPrev = 0;

void setSeed(u64 seed) {
	randPrev = 0;
	randState = seed;
}

u64 random() {
	randPrev = randState * (u64)0x388a2b457eb2cf89;
	randState = randPrev + (randPrev >> 1) + (u64)0x2247aa1637b8f9d1;
	return randState * (u64)0xc6ae4de299a7813d;
}

// Random uniform double from 0 to 1, inclusive.
double rd() {
	return (double)random() / (double)ULLONG_MAX;
}

// Random positive integer with logarithmic distribution.
u64 rl(double average) {
	// Get a random double between 0 and 1.
	double x = rd();
	
	// Apply the logarithmic function to get the result.
	double y = -average * log(x);

	// Take the ceiling of the result to get an integer that is at least 1.
	return (u64)y + 1;
}


// Convert an integer from 0 to 9999 into a string of width 4.
void intToStringFixed(u32 p, char* s) {
	s[3] = '0';
	if (p == 0) return;
	if (p > 9999) {
		s[0] = '9';
		s[1] = '9';
		s[2] = '9';
		s[3] = '9';
		return;
	}

	// Record the last four digits of p (there cannot be more than four digits because of the above check).
	for (int i = 3; p != 0; i--) {
		s[i] = '0' + (p % 10);
		p /= 10;
	}
}

// Convert an integer into a string and return a pointer to the first character after the string.
char* intToString(int p, char* s) {
	if (p == 0) {
		s[0] = '0';
		return s + 1;
	}
	if (p < 0) {
		p *= -1;
		s[0] = '-';
		s++;
	}

	u32 x = 1;
	while (p / x >= 10) {
		x *= 10;
	}

	int i = 0;
	while(x > 0){
		s[i++] = '0' + ((p / x) % 10);
		x /= 10;
	}
	return s + i;
}

// Convert a price from $0.00 to $999.99 into a string of width 6.
void priceToStringFixed(u32 p, char* s) {
	s[2] = '0';
	s[3] = '.';
	s[4] = '0';
	s[5] = '0';
	if (p == 0) return;
	if (p > 99999) {
		s[0] = '9';
		s[1] = '9';
		s[3] = '9';
		s[4] = '9';
		s[5] = '9';
		return;
	}
	
	s[5] = '0' + (p % 10);
	p /= 10;
	s[4] = '0' + (p % 10);
	p /= 10;

	// Record the next three digits of p (there cannot be more than three digits left because of the above check).
	for (int i = 2; p != 0; i--) {
		s[i] = '0' + (p % 10);
		p /= 10;
	}
}

// Convert a price into a string and return a pointer to the first character after the string.
char* priceToString(int p, char* s) {
	if (p < 0) {
		*s = '-';
		s++;
		p *= -1;
	}

	char* s1 = intToString(p / 100, s);
	s1[0] = '.';
	s1[1] = '0' + ((p / 10) % 10);
	s1[2] = '0' + (p % 10);
	return s1 + 3;
}

// Update all limit orders at the given price, removing orders that have been deleted.
void updateLimitOrders(u32 p, u64 t) {
	limitOrder* curr = limitOrderHead[p];
	if (curr != NULL) {
		while (curr->expirationTime <= t) {
			freeLimitOrders[numFreeLimitOrders++] = curr;
			limitOrderHead[p] = curr->next;
			curr = curr->next;
			if (curr == NULL) return;
		}

		while (curr->next != NULL) {
			limitOrder* next = curr->next;
			if (next->expirationTime <= t) {
				freeLimitOrders[numFreeLimitOrders++] = next;
				curr->next = next->next;
			}
			else {
				curr = next;
			}
		}
	}
}

void clearConsole() {

#if defined(_WIN32)
	system("cls");
#endif
#ifdef __linux
	system("clear");
#endif
}

void updateBidAndAsk() {

	while (limitOrderHead[bid] == NULL) {
		bid--;
		if (bid == UINT_MAX) {
			printf("ERROR: Deleted all limit buy orders.\n");
			exit(1);
		}
	}

	while (limitOrderHead[ask] == NULL) {
		ask++;
		if (ask >= NUM_PRICES) {
			printf("ERROR: Deleted all limit sell orders.\n");
			exit(1);
		}
	}
}

// Print the current limit order tape.
void printOrderBook() {

	int numLinesAbovePrice = numOrderBookLines / 2;
	int numLinesBelowPrice = numOrderBookLines - 1 - numLinesAbovePrice;
	u32 price = (bid + ask) / 2;
	u32 minPrice = price - numLinesBelowPrice;
	u32 maxPrice = price + numLinesAbovePrice;

	int lineWidth = 21; // "0000 | 000.00 | 0000n"
	char s[3000];

	for (u32 p = maxPrice; p >= minPrice; p--) {
		int i = maxPrice - p;

		u32 x = 0;
		u32 c = 0;

		// Sum up the total number of shares at this price.
		limitOrder* curr = limitOrderHead[p];
		while (curr != NULL) {
			x += curr->size;
			c++;
			curr = curr->next;
		}

		// Initialize this line.
		for (int j = 0; j < lineWidth; j++) {
			s[i * lineWidth + j] = ' ';
		}
		s[i * lineWidth + 5] = '|';
		s[i * lineWidth + 14] = '|';
		s[i * lineWidth + 20] = '\n';

		// Print this line of the limit order book.
		priceToStringFixed(p, &s[i * lineWidth + 7]);
		if (p <= bid) {
			// Set the buy volume string.
			intToStringFixed(x, &s[i * lineWidth + 0]);
		}
		if (p >= ask) {
			// Set the sell volume string.
			intToStringFixed(x, &s[i * lineWidth + 16]);
		}
	}
	s[numOrderBookLines * lineWidth] = '\0';
	printf("%s\n", s);

	char s0[100];
	char* s1 = priceToString(balance, s0);
	*s1 = 0;
	printf("Balance: %s\n", s0);

	s1 = intToString(sharesOpen, s0);
	*s1 = 0;
	printf("Shares open: %s\n\n", s0);

	printf("%i limit orders\n", numUserLimitOrders);
	int cb = 0, cs = 0;
	for (int i = 0; i < numUserLimitOrders; i++) {
		if (userLimitOrders[i]->p <= bid) cb++;
		if (userLimitOrders[i]->p >= ask) cs++;
	}

	printf("%i limit buys: ", cb);
	for (int i = 0; i < numUserLimitOrders; i++) {
		if (userLimitOrders[i]->p <= bid) {
			s1 = priceToString(userLimitOrders[i]->p, s0);
			*s1 = 0;
			printf("%s ", s0);
			s1 = intToString(userLimitOrders[i]->size, s0);
			*s1 = 0;
			printf("x%s  ", s0);
		}
	}

	printf("\n%i limit sells: ", cs);
	for (int i = 0; i < numUserLimitOrders; i++) {
		if (userLimitOrders[i]->p >= ask) {
			s1 = priceToString(userLimitOrders[i]->p, s0);
			*s1 = 0;
			printf("%s ", s0);
			s1 = intToString(userLimitOrders[i]->size, s0);
			*s1 = 0;
			printf("x%s  ", s0);
		}
	}

	printf("\n\n");

	char* text[5] = { "All          ", "Market Buy:  ", "Market Sell: ", "Limit Buy:   ", "Limit Sell:  "};
	u32 vals[4] = { userMarketBuySize, userMarketSellSize, userLimitBuySize, userLimitSellSize };
	for (int i = 0; i < 5; i++) {
		if (userSelected == i) {
			printf("> ");

			if (userEditing) {
				s1 = intToString(userEditingNumber, s0);
				*s1 = 0;
				printf("%s", s0);
			}
			else {
				printf("%s", text[i]);

				if (i > 0) {
					char* s3 = intToString(vals[i - 1], s0);
					*s3 = 0;
					printf("%s", s0);
				}
			}
		}
		else {
			printf("  ");

			printf("%s", text[i]);

			if (i > 0) {
				char* s3 = intToString(vals[i - 1], s0);
				*s3 = 0;
				printf("%s", s0);
			}
		}
		printf("\n");
	}

	printf("\n\n");
}

// Make and add a new limit order to this price's linked list.
void addLimitOrder(u32 p, u32 size, u64 expirationTime, bool user) {

	// Randomly make a limit order.
	if (numFreeLimitOrders == 0) {
		printf("Ran out of free limit orders available for use.\n");
		exit(1);
	}
	limitOrder* lo = freeLimitOrders[--numFreeLimitOrders];
	lo->next = NULL;
	lo->size = size;
	lo->expirationTime = expirationTime;
	lo->p = p;
	lo->user = user;

	// If the limit order belongs to the user, add it to the list of the user's limit orders.
	if (user) {
		userLimitOrders[numUserLimitOrders++] = lo;
	}

	limitOrder* curr = limitOrderHead[p];
	if (curr == NULL) {
		limitOrderHead[p] = lo;
	}
	else {
		if (fillTiesInStackOrder) {
			// Add from the front and fill from the front.
			lo->next = curr;
			limitOrderHead[p] = lo;
		}
		else {
			// Add from the back and fill from the front.
			while (curr->next != NULL) {
				curr = curr->next;
			}
			curr->next = lo;
		}
	}
}

// Fill orders at one price until size becomes 0. Update the values size and o.
void fillOrders(u32 p, u32* size, u32* o, bool isSell) {
	// Fill orders at this price.
	for (limitOrder* curr = limitOrderHead[p]; curr != NULL; curr = curr->next) {

		u32 s = curr->size;
		if (*size >= s) {
			// Completely fill the limit order and remove it.
			*o += s * p;
			*size -= s;
			freeLimitOrders[numFreeLimitOrders++] = curr;
			if (curr->user) {
				// Completely fill the user's limit order.
				if (isSell) {
					balance -= s * p;
					sharesOpen += s;
				}
				else {
					balance += s * p;
					sharesOpen -= s;
				}

				// Delete the user's limit order.
				for (int i = 0; i < numUserLimitOrders; i++) {
					if (userLimitOrders[i] == curr) {
						numUserLimitOrders--;
						for (int j = i; j < numUserLimitOrders; j++) {
							userLimitOrders[j] = userLimitOrders[j + 1];
						}
						break;
					}
				}
			}
			limitOrderHead[p] = curr->next;
		}
		else {
			// Partially fill the limit order.
			*o += *size * p;
			curr->size -= *size;
			if (curr->user) {
				// Partially fill the user's limit order.
				if (isSell) {
					balance -= *size * p;
					sharesOpen += *size;
				}
				else {
					balance += *size * p;
					sharesOpen -= *size;
				}
			}
			*size = 0;
			break;
		}
	}
}

// Execute a market sell order with a given size at a given time. Return the amount earned in cents.
u32 marketSell(u32 size, u64 t) {
	u32 o = 0;

	for (u32 p = bid; size > 0; p--) {
		if (p == UINT_MAX) {
			printf("ERROR: Filled all buy limit orders with a sell market order. Unable to continue.\n");
			exit(1);
		}

		if (limitOrderHead[p] == NULL) continue;

		bid = p;

		updateLimitOrders(p, t);

		fillOrders(p, &size, &o, 1);
	}

	return o;
}

// Execute a market buy order with a given size at a given time. Return the amount spent in cents.
u32 marketBuy(u32 size, u64 t) {
	u32 o = 0;

	for (u32 p = ask; size > 0; p++) {
		if (p >= NUM_PRICES) {
			printf("ERROR: Filled all sell limit orders with a buy market order. Unable to continue.\n");
			exit(1);
		}

		if (limitOrderHead[p] == NULL) continue;

		ask = p;

		updateLimitOrders(p, t);

		fillOrders(p, &size, &o, 0);
	}

	return o;
}

// Perform the main cycle of creating limit and market orders, deleting orders, and handling the user's orders.
void mainCycle(u64 startingTime) {

	// Initialize the process.
	u64 nextOrderCreation = startingTime;
	u64 targetTime = startingTime;

	while (1) {

		// Do the next order creation.
		if (nextOrderCreation < targetTime) {

			// Choose a limit or market order.
			if (rd() < marketOrderProbability) {
				// Randomly choose a market order size.
				u32 size = rl(averageMarketOrderSize);

				// Choose whether it is a buy or sell.
				if (random() % 2) {
					marketSell(size, nextOrderCreation);
				}
				else {
					marketBuy(size, nextOrderCreation);
				}
			}
			else {

				// Choose whether it is a buy or sell.
				if (random() % 2) {
					// Create a sell limit order above the bid.
					u32 p = bid + rl(averageLimitOrderDistance);
					addLimitOrder(p, rl(averageLimitOrderSize), nextOrderCreation + rl(averageLimitOrderLifespanNS), 0);
					if (p < ask) {
						ask = p;
					}
				}
				else {
					// Create a buy limit order below the ask.
					u32 p = ask - rl(averageLimitOrderDistance);
					addLimitOrder(p, rl(averageLimitOrderSize), nextOrderCreation + rl(averageLimitOrderLifespanNS), 0);
					if (p > bid) {
						bid = p;
					}
				}
			}

			// Randomly generate the next order creation time.
			u64 delta = rl(averageOrderCreationDeltaNS);
			nextOrderCreation += delta;
		}
		else {

			for (u32 p = 0; p < NUM_PRICES; p++) {
				updateLimitOrders(p, targetTime);
			}

			updateBidAndAsk();

			// Print the market.
			clearConsole();
			printOrderBook();

			// Collect the user's input.
			bool buyMarket = 0, sellMarket = 0, buyLimit = 0, sellLimit = 0, tab = 0, enter = 0, backspace = 0;
			bool number[10] = { 0,0,0,0,0,0,0,0,0,0 };
			while (_kbhit()) {
				int c = _getch();
				switch (c) {
				case 46: // .
					buyMarket = 1;
					break;
				case 47: // /
					sellMarket = 1;
					break;
				case 59: // ;
					buyLimit = 1;
					break;
				case 39: // '
					sellLimit = 1;
					break;
				case 9: // TAB
					tab = 1;
					break;
				case 13: // ENTER
					enter = 1;
					break;
				case 8: // BACKSPACE
					backspace = 1;
					break;
				case 27: // ESC
					exit(0);
					break;
				}

				if (c >= 48 && c < 58) {
					number[c - 48] = 1;
				}
			}

			if (buyMarket) {
				// Execute the user's market buy order.
				if (realisticUserMarketOrders) {
					balance -= marketBuy(userMarketBuySize, targetTime);
				}
				else {
					balance -= userMarketBuySize * ask;
				}
				sharesOpen += userMarketBuySize;
				
			}
			if (sellMarket) {
				// Execute the user's market sell order.
				if(realisticUserMarketOrders){
					balance += marketSell(userMarketSellSize, targetTime);
				}
				else {
					balance += userMarketSellSize * bid;
				}
				sharesOpen -= userMarketSellSize;
			}
			if (numUserLimitOrders < MAX_NUM_USER_LIMIT_ORDERS) {
				if (buyLimit) {
					// Create a limit buy order.
					addLimitOrder(bid, userLimitBuySize, ULLONG_MAX, 1);
				}
				else if (sellLimit) {
					// Create a limit sell order.
					addLimitOrder(ask, userLimitSellSize, ULLONG_MAX, 1);
				}
			}

			if (userEditing) {
				for (int i = 0; i < 10; i++) {
					if (number[i] && userEditingNumber < 100000000) {
						userEditingNumber *= 10;
						userEditingNumber += i;
					}
				}
				if (tab || enter) {
					userEditing = 0;
					switch (userSelected) {
					case 0:
						userMarketBuySize = userEditingNumber;
						userMarketSellSize = userEditingNumber;
						userLimitBuySize = userEditingNumber;
						userLimitSellSize = userEditingNumber;
						break;
					case 1:
						userMarketBuySize = userEditingNumber;
						break;
					case 2:
						userMarketSellSize = userEditingNumber;
						break;
					case 3:
						userLimitBuySize = userEditingNumber;
						break;
					case 4:
						userLimitSellSize = userEditingNumber;
						break;
					}
				}
				if (tab) {
					userSelected = (userSelected + 1) % 5;
				}
			}
			else {
				if (tab) {
					userSelected = (userSelected + 1) % 5;
				}
				if (enter) {
					userEditing = 1;
					userEditingNumber = 0;
				}
			}

			if (backspace) {
				// Remove the user's limit orders from the order book.
				for (int i = 0; i < numUserLimitOrders; i++) {
					// By setting the expiration time to 0, the orders will get deleted next time they are updated.
					userLimitOrders[i]->expirationTime = 0;
				}
				numUserLimitOrders = 0;
			}

			targetTime += frameLengthNS;

			// Wait until it is time to begin the next frame.
			while (getTime() < targetTime) {}
		}
	}
}

// Initializes the market to a state where participants are already trading.
void setupMarket(u64 startingTime) {
	bid = rd() * (double)(initialBidMax + 1 - initialBidMin) + (double)initialBidMin;
	u32 spread = rd() * (double)(initialSpreadMax + 1 - initialSpreadMin) + (double)initialSpreadMin;
	ask = bid + spread;

	// Generate limit orders from the bid going down.
	for (u32 p = bid; p >= bid - 10; p--) {
		for (int k = 0; k < 10; k++) {
			addLimitOrder(p, averageMarketOrderSize, startingTime + rl(averageLimitOrderLifespanNS), 0);
		}
	}

	// Generate limit orders from the ask going up.
	for (u32 p = ask; p <= ask + 10; p++) {
		for (int k = 0; k < 10; k++) {
			addLimitOrder(p, averageMarketOrderSize, startingTime + rl(averageLimitOrderLifespanNS), 0);
		}
	}
}

void setup() {
	for (int i = 0; i < NUM_PRICES; i++) {
		limitOrderHead[i] = NULL;
	}

	// Allocate poolSize limit orders and make all of them free limit orders.
	limitOrder* lo = (limitOrder*)calloc(poolSize, sizeof(limitOrder));
	freeLimitOrders = (limitOrder**)calloc(poolSize, sizeof(limitOrder*));
	numFreeLimitOrders = poolSize;
	for (int i = 0; i < poolSize; i++) {
		freeLimitOrders[i] = lo + i;
	}

	numUserLimitOrders = 0;
	userLimitOrders = (limitOrder**)calloc(MAX_NUM_USER_LIMIT_ORDERS, sizeof(limitOrder*));

	setSeed(getTime());
}

int main() {
	setup();

	u64 startingTime = getTime();
	setupMarket(startingTime);

	mainCycle(startingTime);
}
