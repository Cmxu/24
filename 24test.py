import numpy as np
from itertools import combinations

ops = ['/', '-', '*', '+']

def solver(nums, res):
	if len(nums) == 0 and res == 0:
		return True, []
	nums_c = nums.copy()
	for n in nums_c:
		nums.remove(n)
		for op in ops:
			if op == '/':
				w, l = solver(nums, res / n)
			elif op == '-':
				w, l = solver(nums, res - n)
			elif op == '*':
				w, l = solver(nums, res * n)
			else:
				w, l = solver(nums, res + n)
			if w:
				l.append([n, op])
				return True, l
		nums.append(n)
	return False, []

def pretty_format(sol):
	pretty = str(sol[0][0])
	inverse_op = {'+':'-', '-':'+', '*':'/', '/':'x'}
	for i, op in sol[1:]:
		op = inverse_op[op]
		pretty = '(' + pretty + ') ' + op + ' ' + str(i)
	return pretty

def pretty_solver(nums, res):
	a, b = solver(nums, res)
	if a:
		return pretty_format(b)
	else:
		return False

def new_deck():
	return [1,2,3,4,5,6,7,8,9,10,10,10,10]*4

deck = new_deck()

def create_game():
	deck = new_deck()
	np.random.shuffle(deck)
	hand = deck[0:7]
	deck = deck[7:]
	num = []
	while len(num) < 3:
		if deck[0] != 10:
			num.append(deck[0])
		deck = deck[1:]
	return 100*num[0] + 10*num[1] + num[2], hand

def play():
	a, b = create_game()
	print(str(a) + ': ' + str(b))
	return pretty_solver(b, a)
