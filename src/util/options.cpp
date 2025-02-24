/*******************************************************************\

Module: Options

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Options

#include "options.h"
#include <util/exit_codes.h>
#include <iostream>

#include "constructor_of.h"
#include "json.h"
#include "range.h"
#include "string2int.h"
#include "xml.h"

void optionst::set_option(const std::string &option,
                          const std::string &value)
{
  value_listt &value_list=option_map[option];
  value_list.clear();
  value_list.push_back(value);
}

void optionst::set_option(const std::string &option,
                          const bool value)
{
  set_option(option, std::string(value?"1":"0"));
}

void optionst::set_option(const std::string &option, const int value)
{
  set_option(option, std::to_string(value));
}

void optionst::set_option(const std::string &option, const unsigned value)
{
  set_option(option, std::to_string(value));
}

bool optionst::get_bool_option(const std::string &option) const
{
  const std::string value=get_option(option);
  return value.empty()?false:(std::stoi(value)!=0);
}

signed int optionst::get_signed_int_option(const std::string &option) const
{
  const std::string value=get_option(option);
  return value.empty()?0:std::stoi(value);
}

unsigned int optionst::get_unsigned_int_option(const std::string &option) const
{
  const std::string value=get_option(option);
  return value.empty()?0:safe_string2unsigned(value);
}

bool optionst::is_set(const std::string &option) const
{
  return option_map.find(option) != option_map.end();
}

std::vector<int> optionst::is_set_retrace(bool doing_path_exploration) const
{
  if(!doing_path_exploration) {
    std::cerr << "The option '--paths' should be used together with '--retrace'!" << '\n';
    exit(CPROVER_EXIT_USAGE_ERROR);
  }
  auto value_list = option_map.at("retrace");
  if (value_list.empty() || value_list.size() == 0)
  {
    std::cerr << "No input is given!" << '\n';
    exit(CPROVER_EXIT_USAGE_ERROR);
  }
  auto trace_target = value_list.front();
  if(trace_target.empty() || trace_target.length() == 0)
  {
    std::cerr << "Target trace is empty!" << '\n';
    exit(CPROVER_EXIT_USAGE_ERROR);
  }
  std::vector<int> trace;
  for(char& c : trace_target) {
    if (c == '0' || c == '1')
    {
      trace.push_back(c - '0');
    }
    else
    {
      std::cerr << "Target trace is not correctly written, please only use '0' and '1'!" << '\n';
      exit(CPROVER_EXIT_USAGE_ERROR);
    }
  }
  return trace;
}

const std::string optionst::get_option(const std::string &option) const
{
  option_mapt::const_iterator it=
    option_map.find(option);

  if(it==option_map.end())
    return std::string();
  else if(it->second.empty())
    return std::string();
  else
    return it->second.front();
}

const optionst::value_listt &optionst::get_list_option(
  const std::string &option) const
{
  option_mapt::const_iterator it=
    option_map.find(option);

  if(it==option_map.end())
    return empty_list;
  else
    return it->second;
}

/// Returns the options as JSON key value pairs
json_objectt optionst::to_json() const
{
  return make_range(option_map)
    .map([](const std::pair<std::string, value_listt> &option_pair) {
      return std::pair<std::string, json_arrayt>{
        option_pair.first,
        make_range(option_pair.second).map(constructor_of<json_stringt>())};
    });
}

/// Returns the options in XML format
xmlt optionst::to_xml() const
{
  xmlt xml_options("options");
  for(const auto &option_pair : option_map)
  {
    xmlt &xml_option = xml_options.new_element("option");
    xml_option.set_attribute("name", option_pair.first);
    for(const auto &value : option_pair.second)
    {
      xmlt &xml_value = xml_option.new_element("value");
      xml_value.data = value;
    }
  }
  return xml_options;
}

/// Outputs the options to `out`
void optionst::output(std::ostream &out) const
{
  for(const auto &option_pair : option_map)
  {
    out << option_pair.first << ": ";
    bool first = true;
    for(const auto &value : option_pair.second)
    {
      if(first)
        first = false;
      else
        out << ", ";
      out << '"' << value << '"';
    }
    out << "\n";
  }
}
