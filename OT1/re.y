%{
/*********************************************
对正则表达式进行语法分析，返回NFA
允许的输入有：单个字母，空串（用0表示），运算符（ | * ），括号
将所有的词法分析功能均放在 yylex 函数内实现
YACC file
**********************************************/
#include<iostream>
#include<vector>
#include <algorithm>
#include <map>
#include<fstream>
#include<stdio.h>
#include<stdlib.h>
#include<ctype.h>
using namespace std;
int UUID = 0; //标识节点的唯一自增编号
vector<char> input; //记录输入符号

//定义Graph类
class Node{
public:
    int state; //状态编号 使用地址编号
    void* list = nullptr; //边链表
    int attr; //0:start 1:common 2:end

    Node(int at){
        state = UUID++;
        attr = at;
    }
};

class Edge{
public:
    char weight;
    Edge* next = nullptr; //链表中下一条边
    Node* node; //指向的node

    Edge(char w, Node* n){
        weight = w;
        node = n;
    }
};

class Graph{
public:
    vector<Node*> nodes; //NFA中，第一个是start，最后一个是end
};


#ifndef YYSTYPE
#define YYSTYPE Graph*
#endif

int yylex();
extern int yyparse();
FILE* yyin;
void yyerror(const char* s);

//计算ε-closure(T) 用Node*表示状态
vector<Node*> epClosure(vector<Node*> T){
    vector<Node*> ans = T; //ε-closure(T) = T
    vector<Node*> stk = T; //T状态压栈
    while(!stk.empty()){
        //pop t
        Node* t = stk.back();
        stk.pop_back();
        Edge* e = (Edge*)t->list;
        //对每个状态u，t到u有一条ε边
        while(e){
            if(e->weight == '0'){
                Node* u = e->node;
                //如果u不在ε-closure(T)中
                if(std::find(ans.begin(), ans.end(), u) == ans.end()){
                    ans.push_back(u);
                    stk.push_back(u);
                }
            }
            e = e->next;
        }
    }
    return ans;
}


//获取状态T接收a后到达的Node
vector<Node*> delta(vector<Node*> T, char a){
    vector<Node*> ans;
    for(int i=0;i<T.size();i++){
        Node* curr = T[i];
        //遍历curr的所有出边，看是否接收a
        Edge* e = (Edge*)curr->list;
        while(e){
            if(e->weight != a){
                e = e->next;
                continue;
            }
            ans.push_back(e->node);
            e = e->next;
        }
    }
    return ans;
}

//判断DFA状态T是否为终态
bool ifFin(vector<Node*> T){
    for(int i=0;i<T.size();i++){
        Node* curr = T[i];
        if(curr->attr == 2)
            return 1;
    }
    return 0;
}

Graph* NFA_DFA(Graph* g){
    //返回的DFA 首个node为开始节点 也可能同时是终止节点
    Graph* ans = new Graph();

    //初始ε-closure(s0)的Dstates中唯一状态
    vector<Node*> epClos0 = {epClosure({g->nodes[0]})};
    vector<vector<Node*>> Dstates = {epClos0};
    vector<vector<Node*>> unmark = {epClos0}; //记录未标记状态
    //为未标记状态新建DFA中一个节点
    //创建状态到Node的映射
    Node* s0 = new Node(ifFin(epClos0)+1);
    ans->nodes.push_back(s0);
    map<vector<Node*>, Node*> state2node;
    state2node[epClos0] = s0;

    //Dstates存在未标记状态
    while(!unmark.empty()){
        vector<Node*> T = unmark.back();
        unmark.pop_back(); //标记T
        Node* T_node = state2node[T];

        //对于每个输入符号a
        for(int i=0;i<input.size();i++){
            char a = input[i];
            //计算δ(T,a)
            vector<Node*> delta_Ta = delta(T, a);
            //如果delta_Ta为空
            if(delta_Ta.empty())
                continue;
            vector<Node*> U = epClosure(delta_Ta);
            
            //如果U不在Dstates中
            if(std::find(Dstates.begin(), Dstates.end(), U) == Dstates.end()){
                //将U加入Dstates，设置为未标记
                Dstates.push_back(U);
                unmark.push_back(U);
                //为新状态新建节点并加入ans
                Node* n = new Node(ifFin(U)+1);
                ans->nodes.push_back(n);
                state2node[U] = n;
            }
            //Dtran[T,a]=U
            //增加一条T指向U的边
            Node* U_node = state2node[U];
            Edge* e = new Edge(a, U_node);
            //将e接入T_node的出边链表
            e->next = (Edge*)T_node->list;
            T_node->list = e;
            
        }
    }
    return ans;
}

//创建初始分组
vector<vector<Node*>> group_init(Graph* g){
    vector<Node*> T0;
    vector<Node*> T1;
    vector<Node*> T2;
    for(int i=0;i<g->nodes.size();i++){
        Node* curr = g->nodes[i];
        if(curr->attr == 2)
            T2.push_back(curr);
        else        
            T1.push_back(curr);
    }
    //为死状态创建一个节点
    Node* dead = new Node(4);
    T0.push_back(dead);
    return {T0,T1,T2};
}

//确认两点之间是否存在边
bool check_e(Node* src, Node* dst){
    Edge* e = (Edge*)src->list;
    while(e){
        if(e->node == dst)
            return 1;
        e = e->next;
    }
    return 0;
}

Graph* DFAminimize(Graph* g){
    //创建初始分组：死状态T0，非终态T1，终态T2
    vector<vector<Node*>> G = group_init(g);

    //创建原DFA中node到状态T的map
    map<Node*,vector<Node*>> node2T;
    for(int i=0;i<g->nodes.size();i++){
        Node* curr = g->nodes[i];
        if(curr->attr == 2)
            node2T[curr] = G[2];
        else        
            node2T[curr] = G[1];
    }

    //创建待分解状态栈
    vector<vector<Node*>> stk = {G[1], G[2]};

    while(!stk.empty()){
        vector<Node*> currT = stk.back();
        stk.pop_back();

        //currT只有一个node，不可分
        if(currT.size()==1)
            continue;

        for(int i=0;i<input.size();i++){
            char a = input[i];
            //创建状态T到节点集合H的map，表示H接收输入a转换到T
            map<vector<Node*>,vector<Node*>> T2node;
            for(int i=0;i<G.size();i++)
                T2node[G[i]] = {};

            
            //遍历currT所有node，根据接收输入a的转换情况分组
            for(int i=0;i<currT.size();i++){
                Node* n = currT[i];
                Node* n_ = nullptr;
                Edge* e = (Edge*)n->list;
                while(e){
                    if(e->weight == a){
                        n_ = e->node;
                        T2node[node2T[n_]].push_back(n);
                        break;
                    }
                    e = e->next;
                }
                if(!n_)
                    T2node[G[0]].push_back(n);
            }

            //判断a是否可分currT
            //先获取T2node所有的非空value 即新分组
            vector<vector<Node*>> currT_G = {};
            map<vector<Node*>,vector<Node*>>::iterator it;
            for (it = T2node.begin(); it != T2node.end(); ++it){
                if(!it->second.empty())
                    currT_G.push_back(it->second);
            }

            //如果currT可分
            if(currT_G.size() > 1){
                //新分组加入stk
                stk.insert(stk.end(), currT_G.begin(), currT_G.end());
                //从G中删去currT
                for (auto it = G.begin(); it != G.end(); ++it) {
                    if (*it == currT) {
                        G.erase(it);
                        break;
                    }
                }
                //新分组加入G
                G.insert(G.end(), currT_G.begin(), currT_G.end());
                //更新node2T
                for(int i=0;i<currT_G.size();i++){
                    vector<Node*> T_ = currT_G[i];
                    for(int j=0;j<T_.size();j++)
                        node2T[T_[j]] = T_;
                }
                break;
            }
        }
    }

    //遍历G,构建一个新图
    Graph* ans = new Graph();
    //G的一个状态映射到新图上的节点
    map<vector<Node*>,Node*> T2node;
    for(int i=1;i<G.size();i++){
        //对每一个状态T，新建一个节点 如果T中有终态，则n为终态
        Node* n = new Node(1);
        if(G[i][0]->attr == 2)
            n->attr = 2;
        T2node[G[i]] = n;
        ans->nodes.push_back(n);
    }

    Node* ans_start = nullptr;
    //建立节点间边的关系
    for(int i=1;i<G.size();i++){
        Node* curr = T2node[G[i]];
        //遍历状态G[i]中节点
        for(int j=0;j<G[i].size();j++){
            Node* n = G[i][j];
            //如果n是开始节点，则标记curr为开始节点 之后将curr放到ans->nodes的开头
            if(n->attr == 0)
                ans_start = curr;

            Edge* e = (Edge*)n->list;
            while(e){
                //将e转化为新图中的边
                //先找到e指向的节点所属的状态，再转换为新节点
                Node* dst = T2node[node2T[e->node]];
                //如果curr->dst的边不存在，则新建一个边
                if(!check_e(curr,dst)){
                    Edge* new_e = new Edge(e->weight, dst);
                    new_e->next = (Edge*)curr->list;
                    curr->list = new_e;
                }
                e = e->next;
            }
        }
    }
    //将ans_start放到ans->nodes的开头
    for(int i=0;i<ans->nodes.size();i++)
        if(ans->nodes[i] == ans_start){
            ans->nodes[i] = ans->nodes[0];
            ans->nodes[0] = ans_start;
        }
    return ans;
}


%}

//空串：EP  闭包：CLOS 单个字母：LETTER
%token LETTER
%token EP
%token OR CLOS
%token LB RB
%left OR
%right CLOS

%%
lines   :       lines expr ';' { 
            cout<<"VIZ"<<endl;
            //graphviz可视化DFA
            Graph* g1 = DFAminimize(NFA_DFA($2));
            //Graph* g1 = NFA_DFA($2);

            ofstream out("graphviz.dot");
            out << "digraph{\n";

            //遍历g1所有节点
            Node* curr = nullptr;
            out << g1->nodes[0]->state << "[label=\"start\"];"; 
            for(int i=0;i<g1->nodes.size();i++){
                //先声明这个点
                Node* curr = g1->nodes[i];
                //end节点为三角形
                if(curr->attr == 2)
                    out << curr->state << "[shape=triangle];"; 
                out << curr->state << ";\n";
                //对每个节点，遍历所有出边
                Edge* e = (Edge*)curr->list;
                while(e){
                    out << curr->state << "->" << e->node->state << "[label=\"" << e->weight << "\"];\n";
                    e = e->next;
                }
            }
            out << "}";
            out.close();
        }
        |       lines ';'
        |
        ;


expr    :       expr OR expr   {
            //OR的NFA
            Graph* g1 = $1;
            Graph* g2 = $3;

            Node* g1_start = g1->nodes[0];
            Node* g1_end = g1->nodes[g1->nodes.size()-1];
            Node* g2_end = g2->nodes[g2->nodes.size()-1];
            Node* g2_start = g2->nodes[0];

            //创建开始节点
            Node* start = new Node(0);
            //开始节点指向g1_start,g2_start的边
            Edge* e1 = new Edge('0', g1_start);
            Edge* e2 = new Edge('0', g2_start);
            e1->next = e2;
            start->list = (void*)e1;
            //取消g1_start,g2_start的开始标记
            g1_start->attr = 1;
            g2_start->attr = 1;

            //创建结束节点
            Node* end = new Node(2);
            //g1_end,g2_end指向结束节点的边
            Edge* e3 = new Edge('0', end);
            Edge* e4 = new Edge('0', end);
            g1_end->list = (void*)e3;
            g2_end->list = (void*)e4;
            //取消g1_end,g2_end的结束标记
            g1_end->attr = 1;
            g2_end->attr = 1;

            //最后将所有节点加入g1
            //将start节点放到开头
            g1->nodes.insert(g1->nodes.begin(), start);
            //将g2中的节点移到g1
            for(int i=0;i<g2->nodes.size();i++){
                g1->nodes.push_back(g2->nodes[i]);
            }
            //最后放入end
            g1->nodes.push_back(end);

            delete g2;

            $$ = g1;
        } 

        |       expr expr   {
            //连接的NFA
            Graph* g1 = $1;
            Graph* g2 = $2;
            
            //合并g1的end与g2的start
            Node* g1_end = g1->nodes[g1->nodes.size()-1];
            Node* g2_start = g2->nodes[0];

            g1_end->list = g2_start->list; //g1_end获得g2_start所有出边
            g1_end->attr = 1; //变成普通节点
            
            //将g2中的节点移到g1
            for(int i=1;i<g2->nodes.size();i++){
                g1->nodes.push_back(g2->nodes[i]);
            }

            delete g2_start;
            delete g2;

            $$ = g1;
         }
        |	    LB expr RB   { $$ = $2; }
        |       expr CLOS  { 
            Graph* g = $1;

            Node* g_start = g->nodes[0];
            Node* g_end = g->nodes[g->nodes.size()-1];

            //增加g_end->g_start的边
            Edge* e1 = new Edge('0', g_start);
            //g_end会增加两条出边，这涉及到node->list和edge->next

            //创建start和end
            Node* start = new Node(0);
            Node* end = new Node(2);
            //将g_start和g_end变为普通节点
            g_start->attr = 1;
            g_end->attr = 0;

            //start增加两条出边
            Edge* e2 = new Edge('0', g_start);
            Edge* e3 = new Edge('0', end);
            start->list = e2;
            e2->next = e3;

            //增加g_end到end的边
            Edge* e4 = new Edge('0', end);
            g_end->list = e1;
            e1->next = e4;

            //将新增的点加入g
            g->nodes.insert(g->nodes.begin(), start);
            g->nodes.push_back(end);

            $$ = g;
        } 
        |       LETTER  { $$ = $1; }
        |       EP      { $$ = $1; }
        ;

%%

// programs section

int yylex()
{
    int t;
    while(1){
        t=getchar();
        if(t==' '||t=='\t'||t=='\n'){
            //do noting
        }else if(isalpha(t) || t == '0'){
            //创建单个字母 或者 0（ε)的NFA
            Graph *g = new Graph();

            Node *start = new Node(0);
            Node *end = new Node(2);
            Edge *e = new Edge((char)t, end);
            start->list = (void*)e; //将e添加到start的出边
            
            g->nodes.push_back(start);
            g->nodes.push_back(end);
            yylval = g;

            if(t=='0')
                return EP;

            //记录输入符号
            if(std::find(input.begin(), input.end(), (char)t) == input.end()){
                input.push_back((char)t);
            }
            return LETTER;
        }else if(t=='|'){
            return OR;
        }else if(t=='*'){
            return CLOS;
        }else if(t=='('){
            return LB;
        }else if(t==')'){
            return RB;
        }else{
            return t;
        }
    }
}


int main(void)
{   
    yyin=stdin;
    do{
        yyparse();
    }while(!feof(yyin));
    return 0;
}
void yyerror(const char* s){
    fprintf(stderr,"Parse error: %s\n",s);
    exit(1);
}
