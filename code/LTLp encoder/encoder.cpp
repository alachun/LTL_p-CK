// aut2act.cpp : 定义控制台应用程序的入口点。
//

#include <iostream>
#include <fstream>
#include <string>
#include <map>
#include <vector>
#include <sstream>
#include <ctime>
using namespace std;

typedef struct quantifier
{
	string type;
	string obj_type;
	string id;
	vector<string> objects;
}quantifier;

typedef struct tran
{
	string from;
	string to;
	string label;
}tran;

typedef struct FA
{
	vector<string> nodes;
	vector<tran> trans;
}FA;

string change_str(string str)
{
	bool anot = false;
	string str_chan = "";
	if (str.substr(0,1) == "!")
	{
		anot = true;
		str_chan = "(not (";
		str = str.substr(2,str.length()-3);
	}
	else
	{
		str_chan = "(";
		str = str.substr(1,str.length()-2);
	}

	if (str.find("@") != 1)
	{
		int index = str.find("@");
		string left = str.substr(index+1, str.length()-index-1);
		string right = str.substr(0, index);
		str_chan = str_chan + left + " " + right;
	}

	if (anot)
	{
		str_chan = str_chan + "))";
	}
	else
	{
		str_chan = str_chan + ")";
	}

	return str_chan;
}

vector<string> split(string strData)
{
	vector<string> vecData;
	int nPos = strData.find("&&");
    while(nPos > 0)
    {
        string strTmp = strData.substr(0, nPos-1);
        vecData.push_back(strTmp);

        strData.erase(0, nPos+3);
        nPos = strData.find("&&");
    }
	vecData.push_back(strData);

    return vecData;
}

vector<string> split_vee(string strData)
{
	vector<string> vecData;
	int nPos = strData.find("||");
    while(nPos > 0)
    {
        string strTmp = strData.substr(0, nPos-1);
        vecData.push_back(strTmp);

        strData.erase(0, nPos+3);
        nPos = strData.find("||");
    }
	vecData.push_back(strData);

    return vecData;
}

string change_action_str(int n, string tran1, string tran2, string label)
{
	string tran_str = "  (:action trans";
	ostringstream stream;
	stream << n;
	tran_str = tran_str + stream.str() + "\n";
	tran_str = tran_str + "    :precondition (and\n";
	tran_str = tran_str + "                    (aut_mode)\n";
	tran_str = tran_str + "                    (autstate prev_" + tran1 + ")\n";
	if (label.find("&&",0) != -1)
	{
		tran_str = tran_str + "                    ";
		vector<string> conjs = split(label);
		for (int j = 0; j < conjs.size(); j++)
		{
			string pred = "";
			if (conjs[j].find("!", 0) != -1)
			{
				pred = pred + "(not (pos_" + conjs[j].substr(1,conjs[j].length()-1) + "))";
			}
			else
			{
				pred = pred + "(not (neg_" + conjs[j] + "))";
			}
			tran_str = tran_str + pred + " ";
		}
		tran_str = tran_str + "\n";
	}
	else
	{
		if (label != "(1)")
		{
			string pred = "";
			if (label.find("!", 0) != -1)
			{
				pred = pred + "(not (pos_" + label.substr(1,label.length()-1) + "))";
			}
			else
			{
				pred = pred + "(not (neg_" + label + "))";
			}
			tran_str = tran_str + "                    ";
			tran_str = tran_str + pred + "\n";
		}
	}		
	tran_str = tran_str + "                  )\n";

	tran_str = tran_str + "    :effect (and\n";
	tran_str = tran_str + "              (regularize_mode) (not (aut_mode))\n";
	if (label.find("&&",0) != -1)
	{
		tran_str = tran_str + "              ";
		vector<string> conjs = split(label);
		for (int j = 0; j < conjs.size(); j++)
		{
			string pred = "";
			if (conjs[j].find("!", 0) != -1)
			{
				pred = pred + "(neg_" + conjs[j].substr(1,conjs[j].length()-1) + ")";
			}
			else
			{
				pred = pred + "(pos_" + conjs[j] + ")";
			}
			tran_str = tran_str + pred + " ";
		}
		tran_str = tran_str + "\n";
	}
	else
	{
		if (label != "(1)")
		{
			string pred = "";
			if (label.find("!", 0) != -1)
			{
				pred = pred + "(neg_" + label.substr(1,label.length()-1) + ")";
			}
			else
			{
				pred = pred + "(pos_" + label + ")";
			}
			tran_str = tran_str + "              ";
			tran_str = tran_str + pred + "\n";
		}
	}
	tran_str = tran_str + "              ";
	tran_str = tran_str + "(not (autstate prev_" + tran1 + ")) ";
	tran_str = tran_str + "\n";
	tran_str = tran_str + "              (autstate " + tran2 + ") ";
	tran_str = tran_str + "\n";
	tran_str = tran_str + "            )\n";
	tran_str = tran_str + "  )\n";

	return tran_str;
}

int topddl(string inputs[], int n, string outputs[], int n1, string file, ofstream *outfile)
{
	for (int k = 0; k < n; k++)
	{
		string move_str = "";
		ostringstream os;
		os << k;
		move_str = move_str + "  (:action move_" + os.str() + "\n";
		move_str = move_str + "    :precondition (and\n";
		move_str = move_str + "                    (env_mode) (turn" + os.str() + ")\n";
		move_str = move_str + "                  )\n";
		move_str = move_str + "    :effect (and\n";
		move_str = move_str + "              (not (turn" + os.str() + ")) ";
		if (k == n-1)
		{
			move_str = move_str + "(can_switch)\n";
		}
		else
		{
			int m = k+1;
			ostringstream os1;
			os1 << m;
			move_str = move_str + "(turn" + os1.str() + ")" + "\n";
		}
		move_str = move_str + "              (oneof\n";
		move_str = move_str + "                (and (pos_" + inputs[k] + ") (not (neg_" + inputs[k] + ")))\n";
		move_str = move_str + "                (and (neg_" + inputs[k] + ") (not (pos_" + inputs[k] + ")))\n";
		move_str = move_str + "              )\n";
		move_str = move_str + "            )\n";
		move_str = move_str + "  )\n";

		*outfile << move_str;
	}

	string pddl_str = "";
	pddl_str = pddl_str + "  (:action switch2aut\n";
    pddl_str = pddl_str + "    :precondition (and\n";
    pddl_str = pddl_str + "                    (env_mode)\n";
    pddl_str = pddl_str + "                    (can_switch)\n";
	pddl_str = pddl_str + "                  )\n";
    pddl_str = pddl_str + "    :effect (and\n";
    pddl_str = pddl_str + "              (not (env_mode)) (aut_mode) (not (can_switch))\n";
	pddl_str = pddl_str + "            )\n";
    pddl_str = pddl_str + "  )\n";
	*outfile << pddl_str;

	ifstream srcFile(file.c_str(), ios::in); //以文本模式打开in.txt备读
    if (!srcFile) { //打开失败
        cout << "error opening source file." << endl;
        return 0;
    }
	string str;
	vector<string> nodes;
	int i = 0;
	string from = "";
	string label = "";
	string to = "";
	while(getline(srcFile, str)) 
    {
		if (str.find(":",0)!=-1 && str.find("::",0)==-1)
		{			
			int index = str.find(":",0);
			from = str.substr(0,index);
			nodes.push_back(from);
			continue;
		}
		
		if (str.find("::",0)!=-1)
		{
			int index1 = str.find("::",0);
			int index2 = str.find("->",0);
			int index3 = str.find("goto",0);
			label = str.substr(index1+3,index2-3-index1-1);
			to = str.substr(index3+5,str.length()-index3-5);

			if (str.find("||",0) != -1)
			{
				vector<string> disConjs = split_vee(label);
				for (int k = 0; k < disConjs.size(); k++)
				{
					*outfile << change_action_str(i, from, to, disConjs[k].substr(1,disConjs[k].length()-2));
					i++;
				}
			}
			else
			{
				if (label == "(1)")
					*outfile << change_action_str(i, from, to, label);
				else
					*outfile << change_action_str(i, from, to, label.substr(1,label.length()-2));
				i++;
				continue;
			}			
		}

		if (str.find("skip",0) != -1)
		{
			*outfile << change_action_str(i, from, from, "(1)");
			i++;
		}
    }

	pddl_str = "";
	pddl_str = pddl_str + "  (:action refresh\n";
	pddl_str = pddl_str + "    :precondition (and\n";
	pddl_str = pddl_str + "                    (regularize_mode)\n";
	pddl_str = pddl_str + "                  )\n";
	pddl_str = pddl_str + "    :effect (and\n";
	pddl_str = pddl_str + "              (refresh_mode) (not (regularize_mode))\n";
	string regularize = "              ";
	for (int j = 0; j < n; j++)
	{
		regularize = regularize + "(not (pos_" + inputs[j] + ")) (not (neg_" + inputs[j] + ")) ";
	}
	for (int j = 0; j < n1; j++)
	{
		regularize = regularize + "(not (pos_" + outputs[j] + ")) (not (neg_" + outputs[j] + ")) ";
	}
	pddl_str = pddl_str + regularize + "            )\n  )\n";
    *outfile << pddl_str;

	for (int k = 0; k < nodes.size(); k++)
	{
		pddl_str = "";
		ostringstream os2;
		os2 << k;
		pddl_str = pddl_str + "  (:action refresh" + os2.str() + "\n";
		pddl_str = pddl_str + "    :precondition (and\n";
		pddl_str = pddl_str + "                    (refresh_mode)\n";
		pddl_str = pddl_str + "                    (autstate " + nodes[k] + ")\n";
		pddl_str = pddl_str + "                  )\n";
		pddl_str = pddl_str + "    :effect (and\n";
		pddl_str = pddl_str + "              (env_mode) (not (refresh_mode)) (turn0)\n";
		pddl_str = pddl_str + "              ";
		pddl_str = pddl_str + "(not (autstate " + nodes[k] + ")) ";
		pddl_str = pddl_str + "\n";
		if (nodes[k].find("accept") == -1)
			pddl_str = pddl_str + "              (autstate prev_" + nodes[k] + ")\n";
		else
		{
			pddl_str = pddl_str + "              (oneof\n";
			pddl_str = pddl_str + "                (autstate prev_" + nodes[k] + ")\n";
			pddl_str = pddl_str + "                (and (autstate prev_" + nodes[k] + ") (dummy_goal))\n";
			pddl_str = pddl_str + "              )\n";            
		}
		pddl_str = pddl_str + "            )\n";
		pddl_str = pddl_str + "  )\n";
		*outfile << pddl_str;
	}

	pddl_str = "";
	for (int j = 0; j < nodes.size(); j++)
	{
		pddl_str = pddl_str + nodes[j] + " prev_" + nodes[j] + " ";
	}
	pddl_str = pddl_str + "- qstate\n";

	string pos_neg = "";
	for (int k = 0; k < n; k++)
	{
		pos_neg = pos_neg + "(pos_" + inputs[k] + ") (neg_" + inputs[k] + ") ";
	}
	for (int k = 0; k < n1; k++)
	{
		pos_neg = pos_neg + "(pos_" + outputs[k] + ") (neg_" + outputs[k] + ") ";
	}
	pddl_str = pddl_str + pos_neg + "\n";

	string turn = "";
	for (int k = 0; k < n; k++)
	{
		ostringstream os;
		os << k;
		turn = turn + "(turn" + os.str() + ") ";
	}
	pddl_str = pddl_str + turn + "\n";	
	*outfile << pddl_str;

	return 1;
}

FA GetFA(string filePath)
{
	FA fa;

	ifstream faFile(filePath.c_str(), ios::in); 
    if (!faFile) {
        cout << "error opening FA file!" << endl;
        return fa;
    }

	string str;
	vector<string> nodes;
	vector<tran> trans;
	string from = "";
	string label = "";
	string to = "";
	while(getline(faFile, str)) 
    {
		if (str.find(":",0)!=-1 && str.find("::",0)==-1)
		{			
			int index = str.find(":",0);
			from = str.substr(0,index-1);
			nodes.push_back(from);
			continue;
		}
		
		if (str.find("::",0) != -1)
		{
			int index1 = str.find("::",0);
			int index2 = str.find("->",0);
			int index3 = str.find("goto",0);
			label = str.substr(index1+3,index2-3-index1-1);
			to = str.substr(index3+5,str.length()-index3-5);

			if (str.find("||",0) != -1)
			{
				vector<string> disConjs = split_vee(label);
				for (int k = 0; k < disConjs.size(); k++)
				{
					tran t;
					t.from = from;
					t.to = to;
					t.label = disConjs[k].substr(1,disConjs[k].size()-2);
					trans.push_back(t);
				}
			}
			else
			{
				if (label == "(1)")
				{
					tran t;
					t.from = from;
					t.to = to;
					t.label = "true";
					trans.push_back(t);
				}
				else					
				{
					tran t;
					t.from = from;
					t.to = to;
					t.label = label.substr(1,label.size()-2);
					trans.push_back(t);
				}
				continue;
			}			
		}

		if (str.find("skip",0) != -1)
		{
			tran t;
			t.from = from;
			t.to = from;
			t.label = label;
			trans.push_back(t);
		}
    }

	fa.nodes = nodes;
	fa.trans = trans;

	return fa;
}

string Domain_encoding(FA fa, map<string, string> alphabet_table, vector<quantifier> quantifiers)
{
	string predicates = "";
	for (int i = 0; i < fa.nodes.size(); i++)
	{
		predicates = predicates + "(" + fa.nodes[i];
		for (int j = 0; j < quantifiers.size(); j++)
		{
			predicates = predicates + " " + quantifiers[j].id + " - " + quantifiers[j].obj_type;
		}
		predicates = predicates + ") ";
		predicates = predicates + "(prev_" + fa.nodes[i];
		for (int j = 0; j < quantifiers.size(); j++)
		{
			predicates = predicates + " " + quantifiers[j].id + " - " + quantifiers[j].obj_type;
		}
		predicates = predicates + ")\n";
	}
	predicates = predicates + "(aut) (world) ";
	map<string, string>::iterator iter;
	for (iter = alphabet_table.begin(); iter != alphabet_table.end(); iter++)
	{
		string stateFormula = iter->second;
		if (stateFormula.find("pre(") != -1)
		{
			string subStr = stateFormula.substr(stateFormula.find("(")+1, stateFormula.length()-stateFormula.find("("));
			string action_name = subStr.substr(0,subStr.find("("));
			predicates = predicates + "(exec_" + action_name + ") ";
		}
	}

	string aut_act = "";
	aut_act = aut_act + "(:action aut_act\n";
    aut_act = aut_act + " :parameters ()\n";
    aut_act = aut_act + " :precondition (and \n";
	aut_act = aut_act + "                 (aut)\n";
	if (quantifiers.size() != 0)
	{
		for (int i = 0; i < quantifiers.size(); i++)
		{
			if (quantifiers[i].type == "ex")
			{
				aut_act = aut_act + "                 (exist (" + quantifiers[i].id + " - " + quantifiers[i].obj_type + ") \n";
			}
			else
			{
				aut_act = aut_act + "                 (forall (" + quantifiers[i].id + " - " + quantifiers[i].obj_type + ") \n";
			}
		}
	}
	if (fa.nodes.size() == 1)
	{
		aut_act = aut_act + "                 (" + fa.nodes[0] + ")\n";
	}
	else
	{
		aut_act = aut_act + "                 (or (" + fa.nodes[0];
		for (int i = 0; i < quantifiers.size(); i++)
		{
			aut_act = aut_act + " " + quantifiers[i].id;
		}
		aut_act = aut_act + ")";
		for (int i = 1; i < fa.nodes.size(); i++)
		{
			aut_act = aut_act + " (" + fa.nodes[i];
			for (int i = 0; i < quantifiers.size(); i++)
			{
				aut_act = aut_act + " " + quantifiers[i].id;
			}
			aut_act = aut_act + ")";
		}
		aut_act = aut_act + ")\n";
	}
	for (int i = 0; i < quantifiers.size(); i++)
	{
		aut_act = aut_act + "                 )\n";
	}
	aut_act = aut_act + "               )\n";
    aut_act = aut_act + " :effect (and\n";
	aut_act = aut_act + "           (not (aut)) (world)\n";
	for (int i = 0; i < fa.trans.size(); i++)
	{
		string label = "";
		string prop = fa.trans[i].label;
		if (prop.find("!") != -1)
			prop = prop.substr(1,prop.length()-1);
		label = alphabet_table[prop];
		if (label.find("&&") == -1)
		{
			if (label.find("pre(") != -1)
			{
				string subStr = label.substr(label.find("(")+1, label.length()-label.find("("));
				string action_name = subStr.substr(0,subStr.find("("));
				aut_act = aut_act + "           (when (prev_" + fa.trans[i].from;
				for (int i = 0; i < quantifiers.size(); i++)
				{
					aut_act = aut_act + " " + quantifiers[i].id;
				}
				aut_act = aut_act + ") (exec_" + action_name + "))\n";
			}
		}
		else
		{
			vector<string> conjs = split(label);
			bool flag = false;
			int action_index = -1;
			for (int j = 0; j < conjs.size(); j++)
			{
				string subProp = conjs[j];
				if (subProp.find("!") != -1)
					subProp = subProp.substr(1,subProp.length()-1);
				if (alphabet_table[subProp.substr(0,4)] == "pre(")
				{
					flag = true;
					action_index = j;
					break;
				}
			}
			if (flag)
			{
				string subProp = conjs[action_index];
				if (subProp.find("!") != -1)
					subProp = subProp.substr(1,subProp.length()-1);
				string pre_str = alphabet_table[subProp];
				string subStr = pre_str.substr(pre_str.find("(")+1, pre_str.length()-pre_str.find("("));
				string action_name = subStr.substr(0,subStr.find("("));
				aut_act = aut_act + "           (when (and";
				for (int j = 0; j < conjs.size(); j++)
				{
					if (j != action_index)
					{
						string subProp = conjs[j];
						if (subProp.find("!") != -1)
						{
							aut_act = aut_act + " (not (" + alphabet_table[conjs[j].substr(1,conjs[j].length()-1)] + "))";
						}
						else
						{
							aut_act = aut_act + " (" + alphabet_table[conjs[j]] + ")";
						}
					}
				}
				aut_act = aut_act + " (prev_" + fa.trans[i].from;
				for (int i = 0; i < quantifiers.size(); i++)
				{
					aut_act = aut_act + " " + quantifiers[i].id;
				}
				aut_act = aut_act + ")) (exec_" + action_name + "))\n";
			}
		}
	}
	for (int i = 0; i < fa.nodes.size(); i++)
	{
		aut_act = aut_act + "           (when (" + fa.nodes[i];
		for (int i = 0; i < quantifiers.size(); i++)
		{
			aut_act = aut_act + " " + quantifiers[i].id;
		}
		aut_act = aut_act + ") (prev_" + fa.nodes[i];
		for (int i = 0; i < quantifiers.size(); i++)
		{
			aut_act = aut_act + " " + quantifiers[i].id;
		}
		aut_act = aut_act + "))\n";
		aut_act = aut_act + "           (when (not (" + fa.nodes[i];
		for (int i = 0; i < quantifiers.size(); i++)
		{
			aut_act = aut_act + " " + quantifiers[i].id;
		}
		aut_act = aut_act + ")) (not (prev_" + fa.nodes[i];
		for (int i = 0; i < quantifiers.size(); i++)
		{
			aut_act = aut_act + " " + quantifiers[i].id;
		}
		aut_act = aut_act + ")))\n";
	}
	aut_act = aut_act + "         )\n";
	aut_act = aut_act + ")\n";

	string derived_pre = "";
	for (int i = 0; i < fa.nodes.size(); i++)
	{
		derived_pre = derived_pre + "(:derived\n";
		derived_pre = derived_pre + "  (" + fa.nodes[i] + ")\n";
		derived_pre = derived_pre + "  (or\n";

		derived_pre = derived_pre + "    (and\n";
		derived_pre = derived_pre + "	   \n";
		for (int j = 0; j < fa.trans.size(); j++)
		{
			if (fa.trans[j].to == fa.nodes[i])
			{
				derived_pre = derived_pre + "(prev_" + fa.trans[j].from + ") ";
				vector<string> conjs = split(fa.trans[j].label);
				for (int k = 0; k < conjs.size(); k++)
				{
					if (conjs[k].substr(0,4) != "pre(")
					{
						derived_pre = derived_pre + "(" + alphabet_table[conjs[k]] + ") ";
					}
				}
			}
		}
		derived_pre = derived_pre + "    )\n";

		derived_pre = derived_pre + "  )\n";
		derived_pre = derived_pre + ")\n";
	}

	return predicates+aut_act;
}

string Problem_encoding(FA fa, vector<quantifier> quantifiers)
{
	string problem_str = "";

	problem_str = problem_str + "(aut)\n";

	vector<vector<string> > cartesian;
	for (int i = 0; i < quantifiers.size(); i++)
	{
		vector<string> objects = quantifiers[i].objects;
		if (i == 0)
		{
			for (int j = 0; j < objects.size(); j++)
			{
				vector<string> inst;
				inst.push_back(objects[j]);
				cartesian.push_back(inst);
			}
			continue;
		}
		int size = cartesian.size();
		for (int j = 0; j < size; j++)
		{
			for (int k = 0; k < objects.size(); k++)
			{
				vector<string> inst = cartesian[j];
				inst.push_back(objects[k]);
				cartesian.push_back(inst);
			}
		}
		while (size > 0)
		{
			vector<vector<string> >::iterator iter = cartesian.begin();
			cartesian.erase(iter);
			size--;
		}
	}

	for (int i = 0; i < cartesian.size(); i++)
	{
		problem_str = problem_str + "(prev_" + fa.nodes[0];
		for (int j = 0; j < cartesian[i].size(); j++)
		{
			problem_str = problem_str + " " + cartesian[i][j];
		}
		problem_str = problem_str + ")\n";
	}

	if (quantifiers.size() == 0)
		problem_str = problem_str + " (prev_" + fa.nodes[0] + ")\n";

	return problem_str;
}

int main()
{
	clock_t startTime,endTime;
	startTime = clock();

	map<string, string> alphabet_table;
	alphabet_table["p"] = "GOAL(f(x1,x2))";
	alphabet_table["q"] = "pre(a(x,y),x=y)";
	vector<quantifier> quantifiers;
	quantifier quan1;
	quan1.id = "x1";
	quan1.obj_type = "junction";
	quan1.type = "ex";
	string junctions[] = {"junction0","junction1","junction2"};
	for (int i = 0; i < 3; i++)
		quan1.objects.push_back(junctions[i]);
	quantifier quan2;
	quan2.id = "x2";
	quan2.obj_type = "junction";
	quan2.type = "all";
	for (int i = 0; i < 3; i++)
		quan2.objects.push_back(junctions[i]);
	quantifiers.push_back(quan1);
	quantifiers.push_back(quan2);

	string faFile = "fa";
	FA fa = GetFA(faFile);

	string domain_str = Domain_encoding(fa, alphabet_table, quantifiers);
	string problem_str = Problem_encoding(fa, quantifiers);

	ofstream domain_outfile;
	domain_outfile.open("domain_enc", ios::out);  
	if(!domain_outfile.is_open ())
	   	cout << "Open domain_enc file failure!" << endl;
	domain_outfile << domain_str;
	domain_outfile.close();

	ofstream problem_outfile;
	problem_outfile.open("problem_enc", ios::out);  
	if(!problem_outfile.is_open ())
	   	cout << "Open problem_enc file failure!" << endl;
	problem_outfile << problem_str;
	problem_outfile.close();

	endTime = clock();
	cout << "The encoding time is: " <<(double)(endTime - startTime) / CLOCKS_PER_SEC << "s" << endl;





	//string inputs[] = {"r_0", "r_1", "r_2", "r_3", "r_4", "r_5"};
	//string outputs[] = {"g_0", "g_1", "g_2", "g_3", "g_4", "g_5"};

	//ofstream outfile;
	//outfile.open("C:\\Users\\alach\\Desktop\\1.txt", ios::out);  
	//if(!outfile.is_open ())
 //   	cout << "Open file failure" << endl;
	//string filePath = "C:\\Users\\alach\\Desktop\\nba.txt";
	//topddl(inputs, 6, outputs, 6, filePath, &outfile);
	//outfile.close();

	return 0;
}
