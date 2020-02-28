import numpy as np
from itertools import combinations
import time

def make_deck():
    return [1,2,3,4,5,6,7,8,9,10,10,10,10]*4

def create_game(num_cards = 7, digits = 3):
    deck = make_deck()
    np.random.shuffle(deck)
    hand = deck[:num_cards]
    val = list(filter((10).__ne__, deck[num_cards:]))[:digits]
    return hand, sum([val[i] * (10**i) for i in range(digits)])

ops = ['+', '-', '*', '/']
inverse_ops = {'+':'-', '-':'+', '*':'/', '/':'x'}

sv = {}
def brute_speed(hand, val):
    global sv
    if len(hand) == 1 and val == hand[0]:
        return True, []
    hand.sort()
    key = str(hand)
    #key = [0 if i == 10 else i for i in hand]
    #key = sum([key[i]*(10**i) for i in range(len(key))])
    if sv.get(key, False):
        return False, []
    hand_c = hand.copy()
    combos = set(combinations(hand_c, 2))
    for card2, card1 in combos:
        hand.remove(card1)
        hand.remove(card2)
        for op in ops:
            if op == '*':
                hand.append(card1 * card2)
                w, l = brute_speed(hand, val)
                hand.remove(card1 * card2)
            elif op == '+':
                hand.append(card1 + card2)
                w, l = brute_speed(hand, val)
                hand.remove(card1 + card2)
            elif op == '-':
                hand.append(card1 - card2)
                w, l = brute_speed(hand, val)
                hand.remove(card1 - card2)
            elif not card2 == 0:
                hand.append(card1 / card2)
                w, l = brute_speed(hand, val)
                hand.remove(card1 / card2)
            else:
                continue
            if w:
                hand.append(card1)
                hand.append(card2)
                l.append([card1, card2, op])
                return True, l
        hand.append(card1)
        hand.append(card2)
    sv[key] = True
    return False, []

def par_sur(p1):
    if p1[0] == '(' and p1[-1] ==  ')':
        count = 0
        change = False
        for c in p1[:-1]:
            if c == '(':
                change = True
                count += 1
            elif c == ')':
                change = True
                count -= 1
            if change:
                if count == 0:
                    return False
        if change:
            return True
        else:
            return False
    else:
        return False

def opstr(p1, p2, op, par_red):
    if par_red:
        if op == '*':
            return p1 + ' ' + op + ' ' + p2
        elif op == '+':
            p1 = p1[1:-1] if par_sur(p1) else p1
            p2 = p2[1:-1] if par_sur(p2) else p2
            return '(' + p1 + ' ' + op + ' ' + p2 + ')'
        else:
            return '(' + p1 + ' ' + op + ' ' + p2 + ')'
    else:
        return '(' + p1 + ' ' + op + ' ' + p2 + ')'

def evalop(c1, c2, op):
    if op == '+':
        r = c1 + c2
    elif op == '-':
        r = c1 - c2
    elif op == '*':
        r = c1 * c2
    else:
        r = c1 / c2
    return r

def solvable(hand, goal):
    return brute_speed(hand, goal)[0]

def solve(hand, goal):
    return brute_pretty_print(brute_speed(hand, goal)[1], hand)

def brute_pretty_print(sol, hand, par_red = True):
    if not sol:
        return 'No Solution Found'
    stor = {}
    for card in hand:
        if stor.get(card, False):
            stor[card].append(str(card))
        else:
            stor[card] = [str(card)]
    while sol:
        c1, c2, op = sol.pop()
        if c1 == c2:
            if stor.get(c1, False):
                if len(stor[c1]) > 1:
                    p1 = stor[c1][0]
                    stor[c1] = stor[c1][1:]
                    p2 = stor[c2][0]
                    if len(stor[c2]) > 1:
                        stor[c2] = stor[c2][1:]
                    else:
                        stor.pop(c2)
                    r = evalop(c1, c2, op)
                    if stor.get(r, False):
                        stor[r].append(opstr(p1, p2, op, par_red))
                    else:
                        stor[r] = [opstr(p1, p2, op, par_red)]
                else:
                   sol.insert(1, [c1, c2, op])
            else:
                sol.insert(1, [c1, c2, op])
        else:
            if stor.get(c1, False) and stor.get(c2, False):
                p1 = stor[c1][0]
                if len(stor[c1]) > 1:
                    stor[c1] = stor[c1][1:]
                else:
                    stor.pop(c1)
                p2 = stor[c2][0]
                if len(stor[c2]) > 1:
                    stor[c2] = stor[c2][1:]
                else:
                    stor.pop(c2)
                r = evalop(c1, c2, op)
                if stor.get(r, False):
                    stor[r].append(opstr(p1, p2, op, par_red))
                else:
                    stor[r] = [opstr(p1, p2, op, par_red)]
            else:
                sol.insert(1, [c1, c2, op])
    res = stor[list(stor.keys())[0]][0]
    return res[1:-1] if par_sur(res) else res
