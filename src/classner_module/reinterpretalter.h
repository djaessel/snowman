#ifndef REINTERPRETALTER_H
#define REINTERPRETALTER_H

#include <iostream>
#include <QFile>
#include <QTextStream>

#include "specialvals.h"

#include "rawclass.h"

using namespace std;

class ReinterpretAlter
{
public:
  ReinterpretAlter() {}
  void removeReinterpret(vector<RawClass> classList);
};

#endif // REINTERPRETALTER_H
