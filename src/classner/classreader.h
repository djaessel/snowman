#ifndef CLASSREADER_H
#define CLASSREADER_H

#include <map>
#include <filesystem>

#include <QString>

#include "specialvals.h"

#include "fixedclass.h"

using namespace std;
namespace fs = std::filesystem;

class ClassReader
{
private:
  map<QString, FixedClass> classes;
public:
  ClassReader() {}
  void readClasses();
  map<QString, FixedClass> getClasses() {return classes;}
};

#endif // CLASSREADER_H
