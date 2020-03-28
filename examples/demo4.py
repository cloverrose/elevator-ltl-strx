import itertools
import subprocess
import collections
import re

INF = float('inf')

def enum(states):
    flist = []
    for i, v in enumerate(states):
        flist.append('G({0} <-> !({1}))'.format(v, ' || '.join(states[:i] + states[i+1:])))
    return "(" + ' && '.join(flist) + ")"

def oneof(states):
    flist = []
    for i, v in enumerate(states):
        flist.append('G({0} -> !({1}))'.format(v, ' || '.join(states[:i] + states[i+1:])))
    return ' && '.join(flist)


def move(moves):
    al = set()
    for k, vlist in moves.items():
        al.add(k)
    flist = []
    flist.append(enum(list(al)))
    for k, vlist in moves.items():
        vv = vlist + [k]
        flist.append("G({0} -> X({1}))".format(k, ' || '.join(vv)))
    return ' && '.join(flist)

def wrap(x):
    """
    >>> wrap('a')
    'a'

    >>> wrap('a && b')
    '(a && b)'
    """
    if ' ' in x:
        return '(' + x + ')'
    return x

def precondition(a, b):
    """
    a is true if b is true
    """
    a = wrap(a)
    b = wrap(b)
    return "G({1} -> {0})".format(a, b)

def neXt(a, lag):
    """
    >>> neXt('a', 0)
    'a'

    >>> neXt('a', 1)
    'X(a)'

    >>> neXt('a', 2)
    'X(X(a))'
    """
    return 'X(' * lag + a + ')' * lag

def keep(a, end, begin=0):
    """
    keep a between [begin, end] (both begin and end are included)
    if end == INF use G.
    if end == INF use F.

    >>> keep(a, 0)
    'a'

    >>> keep(a, 1)
    '(a && X(a))'

    >>> keep(a, 2)
    '(a && X(a) && X(X(a)))'

    >>> keep(a, 2, 1)
    '(X(a) && X(X(a)))'

    >>> keep(a, INF)
    'G(a)'

    >>> keep(a, INF, 1)
    'X(G(a))'

    >>> keep(a, INF, 2)
    'X(X(G(a)))'

    >>> keep(a, INF, INF)
    'F(G(a))'
    """
    assert end >= begin
    a = wrap(a)
    if end == INF:
        if begin == INF:
            return 'F(G({0}))'.format(a)
        return neXt('G({0})'.format(a), begin)
    flist = []
    for i in range(begin, end + 1):
        flist.append(neXt(a, i))
    return wrap(' && '.join(flist))

def within(a, end, begin=0):
    """
    a should be true at least 1 time between [begin, end], (both begin and end are included)
    if end == INF use F
    if begin == INF use F, but F(F(a)) == F(a)


    >>> within(a, 0)
    'a'

    >>> within(a, 1)
    '(a || X(a))'

    >>> within(a, 2)
    '(a || X(a) || X(X(a)))'

    >>> within(a, 2, 1)
    '(X(a) || X(X(a)))'

    >>> within(a, INF)
    'F(a)'

    >>> within(a, INF, 1)
    'X(F(a))'

    >>> within(a, INF, 2)
    'X(X(F(a)))'

    >>> within(a, INF, INF)
    'F(a)'
    """
    assert end >= begin
    a = wrap(a)
    if end == INF:
        if begin == INF:
            return 'F({0})'.format(a)
        return neXt('F({0})'.format(a), begin)
    flist = []
    for i in range(begin, end + 1):
        flist.append(neXt(a, i))
    return wrap(' || '.join(flist))

def necessary_init(a, b, lag=0):
    """
    At beginning of system, a is necessary for b

    >>> necessary_init('a', 'b', 0)
    '(a R !b)'

    >>> necessary_init('a', 'b', 1)
    '(a R (!b && X(!b)))'
    """
    a = wrap(a)
    b = wrap(b)
    neg_b = '!' + b
    return "({0} R {1})".format(a, keep(neg_b, lag))

def necessary_up_init(a, b, lag=0):
    """
    At beginning of system, up of a `(!a && X(a))` is necessary for b

    >>> necessary_up_init('a', 'b', 0)
    '((!a && X(a)) R (!b && X(!b)))'

    >>> necessary_up_init('a', 'b', 1)
    '((!a && X(a)) R (!b && X(!b) && X(X(!b))))'
    """
    a = wrap(a)
    b = wrap(b)
    neg_b = '!' + b
    return "((!{0} && X({0})) R {1})".format(a, keep(neg_b, lag + 1))

def necessary_again(a, b, lag=0):
    """
    a is necessary for b again. b is free at initial state.

    >>> necessary_anytime('a', 'b', 0)
    'G((b && X(!b)) -> X((a R !b)))'

    >>> necessary_anytime('a', 'b', 1)
    'G((b && X(!b)) -> X((a R (!b && X(!b)))))'
    """
    a = wrap(a)
    b = wrap(b)
    neg_b = '!' + b
    return "G(({1} && X(!{1})) -> X({2}))".format(a, b, necessary_init(a, b, lag))

def necessary_up_again(a, b, lag=0):
    """
    up of a `(!a && X(a))` is necessary for b again. b is free at initial state.

    >>> necessary_up_again('a', 'b', 0)
    'G((b && X(!b)) -> X(((!a && X(a)) R (!b && X(!b)))))'

    >>> necessary_up_again('a', 'b', 1)
    'G((b && X(!b)) -> X(((!a && X(a)) R (!b && X(!b) && X(X(!b))))))'
    """
    a = wrap(a)
    b = wrap(b)
    neg_b = '!' + b
    return "G(({1} && X(!{1})) -> X({2}))".format(a, b, necessary_up_init(a, b, lag))

def keep_until(a, b, lag=0):
    """
    b must hold until a true. b is free at initial state.

    >>> keep_until(a, b, 0)
    'G((!b && X(!!b)) -> X((a R !!b)))'

    >>> keep_until(a, b, 1)
    'G((!b && X(!!b)) -> X((a R (!!b && X(!!b)))))'
    """
    b = wrap(b)
    return necessary_again(a, '!' + b, lag)

def necessary_anytime(a, b, lag=0):
    """
    a is necessary for b

    >>> necessary_anytime('a', 'b', 0)
    '((a R !b) && G((b && X(!b)) -> X((a R !b))))'

    >>> necessary_anytime('a', 'b', 1)
    '((a R (!b && X(!b))) && G((b && X(!b)) -> X((a R (!b && X(!b))))))'
    """
    a = wrap(a)
    b = wrap(b)
    return "(" + necessary_init(a, b, lag) + " && " + necessary_again(a, b, lag) + ")"

def necessary_up_anytime(a, b, lag=0):
    """
    up a `(!a && X(a))` is necessary for b

    >>> necessary_anytime('a', 'b', 0)
    '(((!a && X(a)) R !b) && G((b && X(!b)) -> X(((!a && X(a)) R !b))))'

    >>> necessary_anytime('a', 'b', 1)
    '(((!a && X(a)) R (!b && X(!b))) && G((b && X(!b)) -> X(((!a && X(a)) R (!b && X(!b))))))'
    """
    a = wrap(a)
    b = wrap(b)
    return "(" + necessary_up_init(a, b, lag) + " && " + necessary_up_again(a, b, lag) + ")"

def necessary_again_and_activate(a, b, lag=0):
    return "(" + necessary_again(a, b, lag) + " && " + activate(a, b, INF) + ")"

def necessary_anytime_and_activate(a, b, lag=0):
    return "(" + necessary_anytime(a, b, lag) + " && " + activate(a, b, INF) + ")"

def auto_down_and_necessary_again(a, b, lag=0):
    """
    b can keep only 1 time and a is necessary for b again

    This is same to `auto_down(b) + ' && ' + necessary_again(a, b, lag)` in themantic layer but simpler formula.

    >>> auto_down_and_necessary_again(a,b,0)
    'G(b -> X(a R !b))'

    >>> auto_down_and_necessary_again(a,b,1)
    'G(b -> X(a R (!b && X(!b))))'
    """
    assert lag != INF
    a = wrap(a)
    b = wrap(b)
    neg_b = '!' + b
    return "G({1} -> X({0} R {2}))".format(a, b, keep(neg_b, lag))

def activate(a, b, lag=0):
    """
    a activate b within lag
    lag can be INF.

    >>> activate(a,b,0)
    'G(a -> b)'

    >>> activate(a,b,1)
    'G(a -> (b || X(b)))'

    >>> activate(a,b,2)
    'G(a -> (b || X(b) || X(X(b))))'

    activate(a,b,INF)
    'G(a -> F(b))'
    """
    assert lag >= 0
    a = wrap(a)
    b = wrap(b)
    return "G({0} -> {1})".format(a, within(b, lag))

def deactivate(a, b, lag=0):
    """
    a deactivate b with in lag
    lag can be INF

    >>> deactivate(a,b,0)
    'G(a -> !b)'

    >>> deactivate(a,b,1)
    'G(a -> (!b || X(!b)))'

    >>> deactivate(a,b,2)
    'G(a -> (!b || X(!b) || X(X(!b))))'

    >>> deactivate(a,b,INF)
    'G(a -> F(!b))'
    """
    assert lag >= 0
    b = wrap(b)
    neg_b = '!' + b
    return activate(a, neg_b, lag)

def auto_down(a, lag=1):
    """
    a can keep only lag time.
    lag can be INF

    >>> auto_down(a, 1)
    'G(a -> X(!a))'

    >>> auto_down(a, 2)
    'G(a -> (X(!a) || X(X(!a))))'

    >>> auto_down(a, INF)
    'G(a -> X(F(!a)))'
    """
    assert lag >= 1
    a = wrap(a)
    neg_a = '!' + a
    return "G({0} -> {1})".format(a, within(neg_a, lag, begin=1))

class BinConverter(object):
    def __init__(self, states, prefix):
        self.states = states
        self.prefix = prefix
        self.flist = []

        self.need_flags = len(bin(len(states) - 1)) - 2  # 3状態なら, 00,01,10で表せるので2つのフラグがあればいい
        self.flags = ['{0}{1}'.format(prefix, i) for i in range(self.need_flags)]
        if 2 ** self.need_flags > len(states):
            # 00,01,10,11のうち11は使わない.
            # 全部trueの場合を除けばいい
            self.flist.append('G(' + ' || ' .join(f'!{f}' for f in self.flags) + ')')

        self.values = {}
        for st in states:
            self.values[st] = self.conv(st)

    def conv(self, state):
        """
        convert state to binary representation
        """
        n = self.states.index(state)
        bins = '{{0:0{0}b}}'.format(self.need_flags).format(n)
        fs = []
        for i, c in enumerate(reversed(bins)):
            f = self.flags[i]
            if c == '1':
                fs.append(f)
            else:
                fs.append('!{0}'.format(f))
        return '({0})'.format(' && '.join(fs))

    def __getitem__(self, st):
        return self.values[st]


class NopConverter(object):
    def __init__(self, states, names):
        self.states = states
        self.flags = names
        self.flist = [enum(names)]

        self.values = {}
        for st, nm in zip(states, names):
            self.values[st] = nm

    def __getitem__(self, st):
        return self.values[st]

verified_ver = 2  # ver1 worked at 2020-03-26 15:33

M = 1  # Num of elevator
N = 4  # Num of floor
TL = INF  # timelimit

lft = []
move = []
for j in range(M):
    #lft.append(BinConverter(list(range(N)), 'lft{0}_'.format(j)))
    #move.append(BinConverter(["stop", "up", "down"], 'move{0}_'.format(j)))
    lft.append(NopConverter(list(range(N)), [f'lft{j}_{i}' for i in range(N)]))
    move.append(NopConverter(["stop", "up", "down"], [f"stop{j}", f"up{j}", f"down{j}"]))

# リフト飛び出しボタンが押されたらそれを保存する
go = ["go_{0}".format(i) for i in range(N)]

# リフトを呼ぶボタン
req = ["req_{0}".format(i) for i in range(N)]
# リフトごとのドアの閉開状態
opn = ["open_{0}".format(j) for j in range(M)]


def elevator_phisics(j, N):
    flist = []

    # 急に方向転換できない
    flist.append(f"G({move[j]['up']} -> X({move[j]['stop']} || {move[j]['up']})) && G({move[j]['down']} -> X({move[j]['stop']} || {move[j]['down']}))")
    # 最下階・最上階のときのリフトの動き
    flist.append(f"G({lft[j][0]} -> ({move[j]['stop']} || {move[j]['up']}))")
    flist.append(f"G({lft[j][N-1]} -> ({move[j]['stop']} || {move[j]['down']}))")
    # stop
    for i in range(N):
        flist.append(f"G(({lft[j][i]} && {move[j]['stop']}) -> X({lft[j][i]}))")
    # up
    for i in range(N - 1):
        flist.append(f"G(({lft[j][i]} && {move[j]['up']}) -> X({lft[j][i+1]}))")
    # down
    for i in range(1, N):
        flist.append(f"G(({lft[j][i]} && {move[j]['down']}) -> X({lft[j][i-1]}))")

    # 止まったあと（止まった瞬間は含まない)はドアをOpenできる.
    flist.append(f"G(X({opn[j]}) -> ({move[j]['stop']} && X({move[j]['stop']})))")
    # ドアが空いているならStopしている
    flist.append(f"G({opn[j]} -> {move[j]['stop']})")

    return flist

def some_lift_move(M):
    all_stop = ' || '.join(move[j]['stop'] for j in range(M))
    return f'!({all_stop})'

def elevator_rule(N, M):
    flist = []
    # 呼ばれてないのに動かない
    # flist.append(f"G(({' || '.join(go)}) R ({' && '.join(move[j]['stop'] for j in range(M))}))")
    # flist.append(necessary_anytime(' || '.join(go), '!(' + ' || '.join(move[j]['stop'] for j in range(M)) + ')'))
    flist.append(f"G({some_lift_move(M)} -> ({' || '.join(go)}))")
    return flist

def grant(i):
    # 要求した階にリフトが到着しドアが開いている状態
    return "(" + " || ".join([f"({lft[j][i]} && {opn[j]})" for j in range(M)]) + ")"

assumptions = [
    # 最初はどこも要求していない
    (0, " && ".join(f"!{req[i]}" for i in range(N))),
    # (1, " && ".join(["G(F(!{0}))".format(r) for r in req]))
]

guarantees = [
    (0, ' && '.join(f"!{opn[j]}" for j in range(M))),
    (0, ' && '.join(f"{move[j]['stop']}" for j in range(M))),
    # GOAL リフトを呼び出したらリフトが来る
    (1, ' && '.join(activate(req[i], grant(i), TL) for i in range(N))),
]

for l in lft:
    for x in l.flist:
        guarantees.append((1, x))
for m in move:
    for x in m.flist:
        guarantees.append((1, x))

for j in range(M):
    # phisics constraints
    for f in elevator_phisics(j, N):
        guarantees.append((1, f))

for i in range(N):
    # 要求されたらgoをtrueにする
    guarantees.append((1, f"G((!{grant(i)} && !{go[i]} && {req[i]}) -> X({grant(i)} R {go[i]}))"))
    # リフトが到達してドアを開けたらgoをfalseにする
    guarantees.append((1, f"G(({grant(i)} && !{req[i]}) -> X(!{go[i]}))"))
    # 要求されたときだけgoをtrueにする
    guarantees.append((2, f"G((!{go[i]} && X({go[i]})) -> X({req[i]}))"))
    # goはgrantまで消えない
    guarantees.append((2, keep_until(neXt(grant(i), 1), go[i])))

# rule
for f in elevator_rule(N, M):
    guarantees.append((1, f))

def make_spec(assumptions, guarantees, fname):
    with open(fname, 'w') as fout:
        afirst = True
        fout.write('(\n')
        for v, a in assumptions:
            if afirst:
                afirst = False
            else:
                fout.write(' &&\n')
            fout.write(' ( {0} )\n'.format(a))
        fout.write(') -> (\n')
        gfirst = True
        for v, g in guarantees:
            if gfirst:
                gfirst = False
            else:
                fout.write(' &&\n')
            fout.write(' ( {0} )\n'.format(g))
        fout.write(')\n')

ins = req
outs = []
for l in lft:
    outs += l.flags
for m in move:
    outs += m.flags
outs += opn
outs += go
print('ins=', ins)
print('outs=', outs)
def check_guarantees(assumptions, guarantees, fname, dotfname, svgfname):
    make_spec(assumptions, guarantees, fname)
    p = subprocess.run([
        '/strix/bin/strix', '--kiss',
        # '--minimize',
        '--dot', fname,
        '--ins=' + ','.join(ins),
        '--outs=' + ','.join(outs),
    ], stdout=subprocess.PIPE)
    stdout = p.stdout.decode('utf-8')
    ret = stdout.split('\n')
    if ret[0] != 'REALIZABLE':
        print('UNREALIZABLE')
        return False
    with open(dotfname, 'w') as fout:
        fout.write('\n'.join(ret[1:]))
    # newdotfname = 'h_' + dotfname
    # convert_dot(dotfname, newdotfname)
    newdotfname = dotfname
    p = subprocess.run([
        'dot', '-Tsvg', '-o{}'.format(svgfname), newdotfname], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    # print(p.stdout.decode('utf-8'))
    print('REALIZABLE')
    return True

def check_assumptions(assumptions, fname, dotfname, svgfname):
    make_spec(assumptions, [(-1, '(err && !err)')], fname)
    p = subprocess.run([
        '/strix/bin/strix', '--kiss',
        # '--minimize',
        '--dot', fname,
        '--ins=' + ','.join(ins),
        '--outs=err,' + ','.join(outs),
    ], stdout=subprocess.PIPE)
    stdout = p.stdout.decode('utf-8')
    ret = stdout.split('\n')
    if ret[0] != 'UNREALIZABLE':
        print('invalid assumptions')
        return False
    return True


def main():
    print("START")
    if check_assumptions(assumptions, 'examples/demo4_4f.txt', 'examples/demo4_4f.dot', 'examples/demo4_4f.svg'):
        if check_guarantees(assumptions, guarantees, 'examples/demo4_4f.txt', 'examples/demo4_4f.dot', 'examples/demo4_4f.svg'):
            print('Full specification is realizable')
            return
        print('find wrong guarantee ver>{0}'.format(verified_ver))
        base = [v for v in guarantees if v[0] <= verified_ver]
        targets = [v for v in guarantees if v[0] > verified_ver]
        for ng in range(1, len(targets) + 1):
            print('=' * 80)
            print(ng)
            for cmb in itertools.combinations(targets, ng):
                print(cmb)
                if not check_guarantees(assumptions, base + list(cmb), 'examples/demo4_4f.txt', 'examples/demo4_4f.dot', 'examples/demo4_4f.svg'):
                    return
    else:
        print('find wrong assumption ver>{0}'.format(verified_ver))
        base = [v for v in assumptions if v[0] <= verified_ver]
        targets = [v for v in assumptions if v[0] > verified_ver]
        for ng in range(1, len(targets) + 1):
            print('=' * 80)
            print(ng)
            for cmb in itertools.combinations(targets, ng):
                print(cmb)
                if not check_assumptions(base + list(cmb), 'examples/demo4_4f.txt', 'examples/demo4_4f.dot', 'examples/demo4_4f.svg'):
                    return

if __name__ == '__main__':
    main()
