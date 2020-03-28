import collections
import re

N = 4

def load_dot(dotfile):
    ptn1 = re.compile('(\d+) -> (\d+) \[(.+)\];\n')
    ptn2 = re.compile(r'label="(?P<label>([-\d]+/[-\d]+\\l)+)"')
    graph = collections.defaultdict(list)
    with open(dotfile) as f:
        for l in f:
            mo1 = ptn1.match(l)
            if mo1 is None:
                continue
            node_from, node_to, meta = mo1.groups()
            node_from, node_to = int(node_from), int(node_to)
            mo2 = ptn2.match(meta)
            if mo2 is None:
                continue
            label = mo2.groupdict()['label']
            for s in label.split('\l'):
                if s.strip() == '':
                    break
                ins_v, outs_v = s.split('/')
                ins_cond = []
                outs_signal = []
                for v in ins_v:
                    if v != '-':
                        v = int(v)
                    else:
                        v = -1
                    ins_cond.append(v)
                for v in outs_v:
                    if v != '-':
                        v = int(v)
                    else:
                        v = -1
                    outs_signal.append(v)
                graph[node_from].append((ins_cond, outs_signal, node_to))
    return graph

def match(ins_cond, ins_v):
    for a, b in zip(ins_cond, ins_v):
        if a == -1:
            continue
        if b != a:
            return False
    return True

def convert_input(x):
    if x == '':
        return [0] * N
    ins_v = []
    for c in x:
        ins_v.append(int(c))
    return ins_v

def play(graph):
    cur = 0
    cnt = 0
    while True:
        cnt += 1
        if cnt == 1:
            ins_v = [0] * N
        else:
            x = input('>')
            ins_v = convert_input(x)
            #if ins_v == [0] * N:
            #    print("\033[1A",end="")
        for ins_cond, outs_signal, node_to in graph[cur]:
            if match(ins_cond, ins_v):
                cur = node_to
                viz2(outs_signal)
                break
        else:
            print('Invalid input, your input break the assumption.', ins_v)

def viz2(outs_signal):
    data = []
    states = {
        'no'    : '[{go}]|      |',
        'stop' :  '[{go}]|  ][  |',
        'up'    : '[{go}]|  ↑   |',
        'down'  : '[{go}]|  ↓   |',
        'open'  : '[{go}]|]    [|',
    }
    lft = outs_signal[:N]
    move = outs_signal[N:N+3]
    opn = outs_signal[N+3]
    go = ['o' if v == 1 else ' ' for v in outs_signal[N+4:]]

    for i, l in enumerate(lft):
        assert l != -1
        if l != 1:
            data.append(states['no'].format(go=go[i]))
        else:
            if opn == 1:  # open
                data.append(states['open'].format(go=go[i]))
            else:
                for n, m in zip(['stop', 'up', 'down'], move):
                    if m == 1 or m == -1:
                        data.append(states[n].format(go=go[i]))
                        break

    print('-----------' + '\n'  + '\n'.join(reversed(data)) + "\033[4A",end="")

if __name__ == '__main__':
    graph = load_dot('demo4_4f.dot')
    play(graph)