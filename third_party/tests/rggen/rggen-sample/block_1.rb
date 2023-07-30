# frozen_string_literal: true

register_block {
  name 'block_1'
  byte_size 128
  comment <<~COMMENT
    this is block_1.
    this block includes six registers.
  COMMENT

  register_file {
    name 'register_file_0'
    offset_address 0x00
    register {
      name 'register_0'
      offset_address 0x00
      comment [
        'this is register_0.',
        'bit_field_0 is within this register.'
      ]
      bit_field { name 'bit_field_0'; bit_assignment lsb: 0, width: 8; type :rw; initial_value 0 }
    }
    register {
      name 'register_1'
      offset_address 0x04
      bit_field { name 'bit_field_0'; bit_assignment lsb: 0, width: 8; type :rw; initial_value 0 }
    }
  }

  register_file {
    name 'register_file_1'
    offset_address 0x10
    register {
      name 'register_0'
      offset_address 0x00
      size [2]
      type [
        :indirect,
        'register_file_0.register_0.bit_field_0', ['register_file_0.register_1.bit_field_0', 0]
      ]
      bit_field { name 'bit_field_0'; bit_assignment lsb: 0, width: 8; type :rw; initial_value 0 }
    }
    register {
      name 'register_1'
      offset_address 0x00
      size [2]
      type [
        :indirect,
        'register_file_0.register_0.bit_field_0', ['register_file_0.register_1.bit_field_0', 1]
      ]
      bit_field { name 'bit_field_0'; bit_assignment lsb: 0, width: 8; type :rw; initial_value 0 }
    }
  }

  register_file {
    name 'register_file_2'
    offset_address 0x20
    size [2, step: 32]
    register_file {
      name 'register_file_0'
      register {
        name 'register_0'
        offset_address 0x00
        size [2, 3]
        bit_field { name 'bit_field_0'; bit_assignment lsb:  0, width: 4, sequence_size: 2; type  :rw; initial_value 0 }
        bit_field { name 'bit_field_1'; bit_assignment lsb:  8, width: 4, sequence_size: 2; type :rwe; initial_value 0; reference 'register_file_0.register_0.bit_field_0' }
        bit_field { name 'bit_field_2'; bit_assignment lsb: 16, width: 4, sequence_size: 2; type :rwl; initial_value 0; reference 'register_file_2.register_file_0.register_1.bit_field_0' }
      }
      register {
        name 'register_1'
        offset_address 0x18
        bit_field { name 'bit_field_0'; bit_assignment lsb: 0, width: 1, sequence_size: 2; type :rw; initial_value 0 }
      }
    }
  }
}
